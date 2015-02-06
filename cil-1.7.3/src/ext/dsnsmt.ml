(* TODOS
 * fix Int vs Bool problem - DONE
 * handle conditions from if statements - DONE?
 * handle operators that differ between c and smt eg && vs and
 * remap interpolants when returning them
 * fix the way that I cast if context
 *)

open Cil
open Dsnutils

(* issue if interpolant tries to go past where something is used *)

open String
(* consider using https://realworldocaml.org/v1/en/html/data-serialization-with-s-expressions.html *)

let uninterpretedBitOperators = false

let smtCallTime = ref []

type analysis = 
    UNSATCORE | LINEARSEARCH | BINARYSEARCH | WINDOW | NONINDUCTIVE | NOREDUCTION
let analysis = ref UNSATCORE (*default *)
let summarizeThread = ref false
type multithreadAnalysis = 
    ALLGROUPS | ALLTHREADS | ABSTRACTENV | NOMULTI | PARTITIONTID | PARTITIONGROUP
let multithread = ref NOMULTI
let printTraceSMT = ref false
let printReducedSMT = ref false


(******************************** Optimizations ***************************)
(* keep around the vars for a partition
*)

(*******************************TYPES *************************************)


type varOwner = | Thread of int 
		| Global

type smtVarType = SMTBool | SMTInt | SMTUnknown
    
type smtvar = {fullname : string; 
	       vidx: int; 
	       owner : int; 
	       ssaIdx : int}
    
module VarM = struct 
  type t = smtvar
  let compare x y = Pervasives.compare x y end ;;
(* Given a variable name determine the correct mapping for it *)
module VarMap = Map.Make(VarM)
module VarSet = Set.Make(VarM)
module IntMap = Map.Make(Int)
module VarSSAMap = Map.Make(Int)
module TypeMap = Map.Make(Int)
module StringMap = Map.Make(String)
module StringSet = Set.Make(String)
module TIDSet = Set.Make(Int)
module GroupSet = Set.Make(Int)
module BaseVarSet = Set.Make(Int)
type varSSAMap = smtvar VarSSAMap.t
type varTypeMap = smtVarType TypeMap.t
let emptySSAMap : varSSAMap = VarSSAMap.empty
let emptyTypeMap : varTypeMap = TypeMap.empty
let emptyVarSet = VarSet.empty
let emptyStringSet = StringSet.empty

type term = | SMTRelation of string * term list
	    | SMTConstant of int64
	    | SMTVar of smtvar 
	    | SMTLetVar of string
	    | SMTLetBinding of term * term 
	    | SMTLet of term list * term
	    | SMTTrue | SMTFalse


(* TODO record the program location in the programStmt *)
type clauseType = ProgramStmt of Cil.instr * int option 
		  | Interpolant | Constant | EqTest  
		  | Summary of  (Cil.instr * int option ) list

type sexpType = Sexp | SexpRel | SexpIntConst | SexpVar | SexpBoolConst | SexpLet
type ifContextElem = {iformula : term; istmt : stmt}
type ifContextList = ifContextElem list

type clauseTag = ThreadTag of int | LabelTag of string | SummaryGroupTag of int
let noTags = []

type clause = {formula : term; 
	       idx : int; 
	       vars : VarSet.t; 
	       ssaIdxs : varSSAMap;
	       typ : clauseType;
	       ifContext : ifContextList;
	       cTags : clauseTag list
	      }

type trace = clause list

(* An annotated trace pairs a clause representing an instruction
 * with the term which represents its precondition *)
type annotatedTrace = (term * clause) list
type problemType = CheckSat | GetInterpolation of string | GetUnsatCore
type unsatResult = 
    GotInterpolant of term list | GotUnsatCore of StringSet.t | GotNothing 
type smtResult = Sat | Unsat of unsatResult | Timeout | NoSMTResult
type forwardProp = InterpolantWorks of clause * clause list | NotKLeft | InterpolantFails

exception CantMap of smtvar


(******************** Defs *************************)
let smtDir = "./smt/"
let smtCheckSat = "(check-sat)\n"
let smtGetUnsatCore = "(get-unsat-core)\n"

let smtZero = SMTConstant(0L)
let smtOne = SMTConstant(1L)
let emptyIfContext = []

(******************** Globals *************************)
let count = ref 1
let currentFunc: string ref = ref ""
(*keep the program in reverse order, then flip once. Avoid unneccessary list creation*)
let revProgram : clause list ref = ref [] 
let typeMap : varTypeMap ref  = ref emptyTypeMap
let currentIfContext : ifContextList ref = ref emptyIfContext
let currentThread : int option ref = ref None
let currentLabel : string option ref = ref None
let currentGroup : int option ref = ref None
let threadAnalysis = false
let seenThreads = ref TIDSet.empty
let seenGroups = ref GroupSet.empty


let get_var_type (var : smtvar) : smtVarType = 
  try IntMap.find var.vidx !typeMap 
  with Not_found -> SMTUnknown

let trace_from_at at = 
  let interpolants,trace = List.split at in 
  trace
    
let do_on_trace fn at = fn (trace_from_at at)


(******************** Print Functions *************************)
let string_of_var v = v.fullname

(* DSN TODO replace with list_fold *)

let string_of_vartype typ = 
  match typ with
    |SMTInt -> "Int"
    |SMTBool -> "Bool"
    |SMTUnknown -> "Unknown"

let rec string_of_formula f = 
  let rec string_of_args a = 
    match a with
      | [] -> ""
      | arg :: args -> (string_of_formula arg) ^ " " ^ (string_of_args args)
  in
  match f with
    | SMTLet(b,t) ->
      "(let (" ^ string_of_args b ^ ") " ^ string_of_formula t ^ ")" 
    | SMTLetBinding(v,b) -> "(" ^ string_of_formula v ^ " " ^ string_of_formula b ^ ")"
    | SMTRelation(rel, args) -> 
      "(" ^ rel ^ " " ^(string_of_args args) ^ ")"
    | SMTConstant(i) -> 
      if i < Int64.zero then "(- " ^ Int64.to_string (Int64.abs i) ^ ")"
      else Int64.to_string i
    | SMTVar(v) -> string_of_var v
    | SMTLetVar(v) -> v
    | SMTFalse -> "false"
    | SMTTrue -> "true"
let string_of_term = string_of_formula

let string_of_clause c = 
  string_of_formula c.formula

let string_of_ifcontext ic = 
  let rec aux ic acc = 
    match ic with 
      | [] -> acc
      | [x] ->  "if (" ^ acc ^  string_of_formula x.iformula ^ ")\n"
      | x::xs -> aux xs (acc ^ string_of_formula x.iformula ^ " && ") 
  in
  aux ic ""

let string_of_tag  = function 
  | ThreadTag i -> "Thread_" ^ string_of_int i
  | LabelTag s -> "Label_" ^ s
  | SummaryGroupTag g -> "Group_" ^ string_of_int g

let string_of_tags tags = List.fold_left (fun a x -> "//" ^ string_of_tag x ^ "\n" ^ a) "" tags

let rec label_string = function
  | LabelTag _ as l :: _ -> string_of_tag l
  | x::xs -> label_string xs
  | [] -> ""

let string_of_cprogram c =
  match c.typ with 
    | ProgramStmt (i,Some tid) -> 
      d_string "//Tid %d\n%s%a" tid 
	(string_of_ifcontext c.ifContext)  
	d_instr i
    | ProgramStmt (i,None) -> 
      d_string "%s%a" (string_of_ifcontext c.ifContext)  d_instr i
    | Interpolant | Constant -> "//" ^ string_of_formula c.formula
    | EqTest -> failwith "shouldn't have equality tests in the final program"
    | Summary _ -> "//(Summary)\n//" ^ string_of_formula c.formula

let string_of_cl cl = List.fold_left (fun a e -> a ^ string_of_clause e ^ "\n") "" cl
let string_of_formlist fl = List.fold_left (fun a e -> a ^ string_of_formula e ^ "\n") "" fl

let debug_var v = 
  "{name: " ^ v.fullname 
  ^  " vidx: " ^ (string_of_int v.vidx)
  ^  " owner: " ^ (string_of_int v.owner)
  ^  " ssaIdx: " ^ (string_of_int v.ssaIdx)
  ^ "}"
let rec debug_args a = 
  match a with
    | [] -> ""
    | arg :: args -> (debug_formula arg) ^ " " ^ (debug_args args)
and debug_formula f = 
  match f with
    | SMTLet(b,t) ->
      "(let ((" ^ debug_args b ^ " " ^ debug_formula t ^ ")) " 
    | SMTRelation(rel, args) -> 
      "\t(" ^ "Rel: " ^ rel ^ " args: " ^(debug_args args) ^ ")"
    | SMTConstant(i) -> Int64.to_string i
    | SMTVar(v) -> debug_var v
    | SMTLetVar(v) -> v
    | SMTFalse | SMTTrue -> string_of_formula f
    | SMTLetBinding (v,e) -> debug_formula v ^ " " ^ debug_formula e

(* could make tail rec if I cared *)
let debug_SSAMap m = 
  let string_of_binding (k,v) = "\t(" ^ string_of_int k ^ ", " ^ debug_var v ^ ")\n" 
  in List.fold_left (fun a e -> (string_of_binding e) ^ a) "" (VarSSAMap.bindings m)

let debug_vars vars = 
  List.fold_left (fun a e -> "\t" ^ debug_var e ^ "\n" ^ a) "" (VarSet.elements vars)
    
let  debug_clause c = 
  "\nidx: " ^ (string_of_int(c.idx))
  ^"\n\tsexp: " ^ string_of_formula c.formula
  (* ^ "\n\tformula:\n" ^ (debug_formula c.formula)  *)
  ^ "\n\tSSA:\n" ^ debug_SSAMap c.ssaIdxs
  ^ "\n\tvars:\n" ^ debug_vars c.vars

let debug_typemap () = 
  let fold_fn v t a = 
    a ^ "\n" ^ (string_of_int v) ^ " " ^ (string_of_vartype t)
  in
  TypeMap.fold fold_fn !typeMap ""

let assertion_name (c : clause) :string = 
  let prefix = label_string c.cTags in
  match c.typ with
    | ProgramStmt(_) -> prefix ^ "PS_" ^ (string_of_int c.idx)
    | Interpolant -> "IP_" ^ (string_of_int c.idx)
    | Constant -> "CON_" ^ (string_of_int c.idx)
    | EqTest -> "EQTEST_" ^ (string_of_int c.idx)
    | Summary _ -> failwith "should not be asserting summaries"

let make_flowsensitive_formula c =
  let make_ifContext_formula ic = 
    match ic with 
      | [] -> SMTTrue
      | [x] -> x.iformula
      | _ -> SMTRelation("and", List.map (fun x -> x.iformula) ic)
  in
  if c.ifContext <> [] then
    SMTRelation("=>", [make_ifContext_formula c.ifContext;c.formula])
  else
    c.formula

let make_assertion_string flowSensitive c =
  let form = if flowSensitive then make_flowsensitive_formula c else c.formula in 
  "(assert (! " 
  ^ string_of_formula form
  ^ " :named " ^ assertion_name c
  ^ "))\n"

(* DSN THIS IS A HORRID HACK FIX THIS LATER *)
(* HACK HACK HACK *)
let make_abstract_env_assertion_string localTid c = 
  match c.typ with
    | ProgramStmt(_,None) -> failwith "expected a tid here"
    | ProgramStmt(instr, Some thatTid) when thatTid <> localTid ->
      make_assertion_string false c
    | _ ->
      make_assertion_string true c

(* by default, just use the standard make assertion string. Be flow sensitive *)
let assertionStringFn = ref (make_assertion_string true)
  
let make_var_decl v =
  let ts = string_of_vartype (get_var_type v) in
  "(declare-fun " ^ (string_of_var v)  ^" () " ^ ts ^ ")\n" 
let print_linenum c = 
  match c.typ with 
    | ProgramStmt (i,_) -> d_string "%a" d_loc (get_instrLoc i)
    | _ -> ""

let print_formulas x = 
  List.iter (fun f -> Printf.printf "%s\n" (string_of_formula f)) x; 
  flush stdout
let print_clauses x = 
  List.iter (fun f -> Printf.printf "%s\n" (string_of_clause f)) x; 
  flush stdout
let print_cprogram x = 
  List.iter (fun f -> Printf.printf "%s\n" (string_of_cprogram f)) x; 
  flush stdout
let print_annotated_trace  ?(stream = stdout) x = 
  List.iter (fun (t,c) -> Printf.fprintf stream "\n//%s\n%s\n" (string_of_formula t)
    (string_of_cprogram c)) x; 
  flush stream
let print_trace_linenums x = List.iter (fun c -> Printf.printf "%s\n" (print_linenum c)) x;
  flush stdout
let print_annotatedtrace_linenums x = List.iter (fun (_,c) -> Printf.printf "%s\n" (print_linenum c)) x;
  flush stdout

(* could make tailrec by using revmap *)
let reduced_linenums x = 
  let nums = List.map print_linenum x in
  let nums = List.filter (fun x -> x <> "") nums in
  compress nums

let reduced_linenums_at x = 
  let interpolants,trace = List.split x in
  reduced_linenums trace

let print_reduced_linenums x = 
  let reduced = reduced_linenums x in
  List.iter (Printf.printf "%s\n") reduced



(****************************** Clauses ******************************)
(* two possibilities: either maintain a mapping at each point
 * or remap as we go starting from one end *)


(* So we need to figure out the type of each variable *)



(* this function does two things: It determines the type of the 
 * expression.  It also updates the mapping with any newly discovered
 * var -> type mappings
 *)

let all_vars clauses = List.fold_left (fun a e -> VarSet.union e.vars a) emptyVarSet clauses

let all_basevars clauses = 
  let allVars = all_vars clauses in
  VarSet.fold (fun e a -> BaseVarSet.add e.vidx a) allVars BaseVarSet.empty

let count_basevars clauses = 
  BaseVarSet.cardinal (all_basevars clauses)

let count_basevars_at a = 
  let interpolants,trace = List.split a in
  count_basevars trace

let type_check_and_cast_to_bool topForm = 
  let updatedVar = ref false in
  let types_match t1 t2 =
    match t1,t2 with
      | SMTUnknown,_ | SMTInt,SMTInt | SMTBool,SMTBool -> true
      | _ -> false
  in
  let second_if_matching t1 t2 = 
    if types_match t1 t2 then t2 else failwith "mismatching types"
  in
  let update_type (var : smtvar) newType = 
    let currentType = get_var_type var  in
    match (currentType,newType) with 
      | SMTUnknown,SMTBool | SMTUnknown,SMTInt ->  
	typeMap := TypeMap.add var.vidx newType !typeMap;
	updatedVar := true
      | _ -> ()
  in
  let rec analyze_type f = 
    match f with 
      | SMTLetBinding _ -> failwith "shouldn't be parsing this!"
      | SMTLet _ -> failwith "shouldn't be parsing this!"
      | SMTLetVar _ -> failwith "shouldn't be parsing this!"
      | SMTFalse | SMTTrue -> SMTBool
      | SMTConstant(_) -> SMTInt
      | SMTVar(v) -> get_var_type v
      | SMTRelation(s,l) -> begin
	match s with 
	  | "ite" -> begin
	    match l with 
	      |	[i;t;e] -> 
		if not (types_match (analyze_type i) SMTBool) then failwith "not bool!";
		analyze_type_lst [t;e] 
	      | _ -> failwith "bad ite"
	  end 
	  | "<" | ">" | "<=" | ">=" -> (*int list -> bool *)
	    SMTBool
	  | "and" | "or" | "xor" | "not" -> (*bool list -> bool*)
	    SMTBool
	  | "=" | "distinct" ->
	    SMTBool
	  | "+" | "-" | "*" | "div" | "mod" | "abs" -> 
	    SMTInt
	  | "band" | "bxor" | "bor" | "shiftlt" | "shiftrt" ->
	    if not uninterpretedBitOperators then failwith "not supporting bit operators";
	    SMTInt
	  | _ -> failwith ("unexpected operator in analyze type |" ^ s ^ "|")
      end
  and analyze_type_lst l = List.fold_left 
    (fun a x -> second_if_matching a (analyze_type x)) SMTUnknown l
  in
  let rec assign_vartypes desired f =
    match f with
      | SMTLetBinding _ -> failwith "shouldn't be parsing this!"
      | SMTLet _ -> failwith "shouldn't be parsing this!"
      | SMTLetVar _ -> failwith "shouldn't be parsing this!"
      | SMTFalse | SMTTrue | SMTConstant _ -> ()
      | SMTVar(v) -> update_type v desired
      | SMTRelation(s,l) -> begin
	match s with 
	  | "ite" -> begin
	    match l with 
	      |	[i;t;e] -> 
		assign_vartypes SMTBool i;
		let tl = analyze_type_lst [t;e] in
		List.iter (assign_vartypes tl) [t;e]
	      | _ -> failwith "bad ite"
	  end 
	  | "<" | ">" | "<=" | ">=" -> (*int list -> bool *)
	    List.iter (assign_vartypes SMTInt) l
	  | "and" | "or" | "xor" | "not" -> (*bool list -> bool*)
	    List.iter (assign_vartypes SMTBool) l
	  | "=" | "distinct" ->
	    let tl = analyze_type_lst l in
	    List.iter (assign_vartypes tl) l
	  | "+" | "-" | "*" | "div" | "mod" | "abs" -> 
	    List.iter (assign_vartypes SMTInt) l
	  | "band" | "bxor" | "bor" | "shiftlt" | "shiftrt" ->
	    if not uninterpretedBitOperators then failwith "not supporting bit operators";
	    List.iter (assign_vartypes SMTInt) l
	  | _ -> failwith ("unexpected operator in analyze type |" ^ s ^ "|")
      end
  in
  let make_cast desired f = 
    let unknown_to_int t = match t with 
      | SMTUnknown -> SMTInt
      | _ -> t
    in
    (* treating unknown as int *)
    match unknown_to_int (analyze_type f), unknown_to_int desired  with
      | SMTBool, SMTInt ->
	SMTRelation("ite",[f;smtOne;smtZero])
      | SMTInt, SMTBool -> 
	SMTRelation("distinct",[f;smtZero])
      | SMTBool,SMTBool | SMTInt,SMTInt -> f
      | _ -> failwith "wtf in make cast"
  in
  let rec rec_casts desired f = 
    match f with
      | SMTLetBinding _ -> failwith "shouldn't be parsing this!"
      | SMTLet _ -> failwith "shouldn't be parsing this!"
      | SMTLetVar _ -> failwith "shouldn't be parsing this!"
      | SMTFalse | SMTTrue | SMTConstant _ | SMTVar _ -> make_cast desired f
      | SMTRelation(s,l) -> begin
	match s with 
	  | "ite" -> begin
	    match l with 
	      |	[i;t;e] -> 
		let i = rec_casts SMTBool i in
		let tl = analyze_type_lst [t;e] in
		let t = rec_casts tl t in
		let e = rec_casts tl e in
		make_cast desired (SMTRelation(s,[i;t;e]))
	      | _ -> failwith "bad ite"
	  end 
	  | "<" | ">" | "<=" | ">=" -> (*int list -> bool *)
	    let l = List.map (rec_casts SMTInt) l in
	    make_cast desired (SMTRelation(s,l))
	  | "and" | "or" | "xor" | "not" -> (*bool list -> bool*)
	    let l = List.map (rec_casts SMTBool) l in
	    make_cast desired (SMTRelation(s,l))
	  | "=" | "distinct" ->
	    let tl = analyze_type_lst l in
	    let l = List.map (rec_casts tl) l in
	    make_cast desired (SMTRelation(s,l))
	  | "+" | "-" | "*" | "div" | "mod" | "abs" -> 
	    let l = List.map (rec_casts SMTInt) l in
	    make_cast desired (SMTRelation(s,l))
	  | "band" | "bxor" | "bor" | "shiftlt" | "shiftrt" ->
	    if not uninterpretedBitOperators then failwith "not supporting bit operators";
	    let l = List.map (rec_casts SMTInt) l in
	    make_cast desired (SMTRelation(s,l))
	  | _ -> failwith ("unexpected operator in analyze type |" ^ s ^ "|")
      end
  in
  let rec findfixpt top = 
    updatedVar := false;
    assign_vartypes SMTBool top;
    if !updatedVar then findfixpt top else ()
  in
  findfixpt topForm;
  rec_casts SMTBool topForm

(* not tail recursive *)
let rec get_vars formulaList set = 
  match formulaList with 
    | [] -> set
    | x::xs ->
      let set = get_vars xs set in
      match x with
	| SMTRelation(s,l) -> get_vars l set
	| SMTLet(b,t) -> get_vars b (get_vars [t] set)
	| SMTConstant _ | SMTFalse | SMTTrue | SMTLetVar _ -> set
	| SMTVar(v) -> VarSet.add v set 
	| SMTLetBinding(v,e) -> get_vars [e] set

let get_vars_ic icList set = 
  List.fold_left (fun a e -> get_vars [e.iformula] a) set icList

let rec make_ssa_map (vars : smtvar list) (ssaMap : varSSAMap) : varSSAMap =
  match vars with 
    | [] -> ssaMap
    | v :: vs -> 
      let vidx = v.vidx in
      let ssaMap = 
	try let vOld = VarSSAMap.find vidx ssaMap in
	    if vOld.ssaIdx < v.ssaIdx then
	      VarSSAMap.add vidx v ssaMap
	    else
	      ssaMap
	with Not_found -> VarSSAMap.add vidx v ssaMap
      in
      make_ssa_map vs ssaMap

let make_clause (f: term) (ssa: varSSAMap) (ic : ifContextList) 
    (ct: clauseType) (tags : clauseTag list)
    : clause = 
  incr count;
  let v  = get_vars [f] emptyVarSet in
  let v = get_vars_ic ic v in
  let ssa  = make_ssa_map (VarSet.elements v) ssa in
  let f = match ct with
    | ProgramStmt _ ->  type_check_and_cast_to_bool f
    | _ -> f
  in
  let c  = {formula = f; 
	    idx = !count; 
	    vars = v; 
	    ssaIdxs = ssa; 
	    typ = ct; 
	    ifContext = ic;
	    cTags = tags
	   } in
  c

let make_true_clause () = make_clause SMTTrue emptySSAMap emptyIfContext Constant noTags
let make_false_clause () =  make_clause SMTFalse emptySSAMap emptyIfContext Constant noTags
let negate_clause cls = {cls with formula = SMTRelation("not",[cls.formula])}


(****************************** Remapping ******************************)
(* TODO need to decide what to do if there is no mapping i.e. we've gone 
 * before the first def.  Options include 
 * throw an exception
 * let it be havoced i.e. have a blank 0 mapping for all vars
 *)

let get_current_var oldVar ssaMap = 
  try Some (VarSSAMap.find oldVar.vidx ssaMap)
  with Not_found -> None

let remap_formula ssaMap form =
  let rec aux = function 
    | SMTLetBinding(v,e) -> SMTLetBinding(v,aux e)
    | SMTLet(b,t) -> 
      SMTLet(List.map aux b, aux t)
    | SMTRelation(s,tl) ->
      SMTRelation(s,List.map aux tl)
    | SMTConstant(_) | SMTFalse | SMTTrue | SMTLetVar _ as form -> form
    | SMTVar(v) ->
      let newVarOpt = get_current_var v ssaMap in
      match newVarOpt with
	| Some (newVar) -> SMTVar(newVar)
	| None -> raise (CantMap v)
  in
  aux form
    

(* I guess we should remap the if context too.  Does this make sense? 
 * Also, there is a bug where we ended up with two clauses with the same interpolation
 * id.  Make a new clause with a new id
 * possibly just assert that the if context is empty
 *)
let remap_clause ssaMap cls = 
  make_clause 
    (remap_formula ssaMap cls.formula) 
    ssaMap 
    (List.map (fun x -> {x with iformula = remap_formula ssaMap x.iformula}) cls.ifContext)
    cls.typ    
    cls.cTags



(******************** File creation ********************)

let make_all_interpolants program =
  let str = List.fold_left (fun accum elem -> accum ^ " " ^ (assertion_name elem)) "" program in
  "(get-interpolants " ^ str ^ ")\n"

let make_interpolate_between before after = 
  let string_of_partition part = 
    match part with 
      | [] -> failwith "should be a partition"
      | [x] -> assertion_name x
      | _ -> 
	let names = List.fold_left 
	  (fun accum elem -> (assertion_name elem) ^ " " ^ accum) "" part in
	"(and " ^ names ^ ")"
  in
  let beforeNames = string_of_partition before in
  let afterNames = string_of_partition after in
  "(get-interpolants " ^ beforeNames ^ " " ^ afterNames ^ ")\n"

let print_to_file filename lines = 
  let oc = open_out filename in    (* create or truncate file, return channel *)
  let printf_oc = Printf.fprintf oc "%s" in
  List.iter printf_oc lines;
  close_out oc                (* flush and close the channel *)
    
let print_annotated_trace_to_file filename trace = 
  let oc = open_out (filename ^ ".txt") in 
  print_annotated_trace ~stream:oc trace;
  close_out oc

(******************** Input functions *************************)

(* for now only worry about ' ' *)
(* ocaml 4.0 would allow trim *)
let trim_left str = 
  let rec trim_rec_left str i = 
    if i = length str || str.[i] <> ' ' then i
    else trim_rec_left str (i + 1)
  in
  trim_rec_left str 0

let trim_right str = 
  let rec trim_rec_right str i = 
    if i < 0 || str.[i] <> ' ' then i
    else trim_rec_right str (i - 1)
  in 
  trim_rec_right str ((length str) -1)

let trim str =
  if (contains str ' ' )then 
    let l_idx = trim_left str in
    let r_idx = trim_right str in
    let len = r_idx - l_idx + 1  in 
    let len = if (len < 0) then 0 else len in
    sub str l_idx len
  else 
    str

let getFirstArgType str = 
  let str = trim str in
  match str.[0] with
    | '(' 
      -> Sexp
    | '0' | '1' | '2' | '3' | '4'
    | '5' | '6' | '7' | '8' | '9' 
      -> SexpIntConst
    | '=' | '<'  | '>' 
    | '-' | '+'  | '*' 
      -> SexpRel
    | _ 
      -> begin match str with 
	|  "and" | "distinct" | "or" | "not" | "xor" | "ite" 
	  -> SexpRel
	| "let" 
	  -> SexpLet
	| "band" | "bxor" | "bor" | "shiftlt" | "shiftrt" 
	  -> if not uninterpretedBitOperators then failwith "not supporting bit operators";
	    SexpRel
	| "false" | "true" 
	  -> SexpBoolConst
	| _ 
	  -> SexpVar
      end

let split_on_underscore str = Str.split (Str.regexp "[_]+") str
let is_cse_var str = Str.string_match (Str.regexp ".cse[0-9]+") str 0

(* canonical format: x_vidx_ssaidx *)
let smtVarFromString str = 
  match split_on_underscore str with
    | [prefix;vidxStr;ssaIdxStr] -> 
      if prefix <> "x" then failwith ("invalid prefix " ^ prefix);
      {fullname = str; 
       vidx = (int_of_string vidxStr);
       ssaIdx =  (int_of_string ssaIdxStr);
       owner = -1
      }
    | _ -> failwith ("variable " ^ str ^ "is not in the valid format")
      
let rec matchParensRec str i level = 
  if level = 0 then 
    i - 1 
  else if str.[i] = '(' then 
    matchParensRec str (i+1) (level +1)
  else if str.[i] = ')' then
    matchParensRec str (i+1) (level -1)
  else 
    matchParensRec str (i+1) level

let findEndOfWord str = 
  if not (contains str ' ') then 
    length str 
  else
    index str ' '

(*if the entire expression is in parens, strip them away *)
let rec strip_parens str =
  let str = trim str in
  let len = length str in
  if len >= 2 && str.[0] = '(' && (matchParensRec str 1 1 = len - 1) then
    let toStrip = sub str 1 (len - 2) in
    strip_parens toStrip
  else 
    str

let extract_unsat_core (str) : string list = 
  let str = strip_parens str in
  Str.split (Str.regexp "[ \t]+") str

let rec extract_term (str)  : term list = 
  (* returns the first sexp as a string,
   * and the remainder as another string *)
  let extract_first_sexp str = 
    let str = trim str in
    let len = length str in
    if len = 0 then failwith "nothing here"
    else if (str.[0] = '(') then
      let endIdx = matchParensRec str 1 1 in 
      let lhs = sub str 0 (endIdx +1) in 
      (* +1 avoid the closing paren *)
      let rhs = sub str (endIdx + 1) (len - endIdx - 1) in
      (trim lhs, trim rhs)
    else 
      let endIdx = findEndOfWord str in
      if endIdx = len then 
	(str,"")
      else 
	let lhs = sub str 0 (endIdx) in 
	let rhs = sub str (endIdx + 1) (length str - endIdx - 1) in
	(trim lhs, trim rhs)
  in
  let str = strip_parens (trim str) in
  if length str = 0 then 
    []
  else
    let headStr, tailStr = extract_first_sexp str in
    match getFirstArgType headStr with
      | Sexp -> 
	let headExpLst = extract_term headStr in
	let tailExp = extract_term tailStr in
	let rec foldHeadLst l = 
	  match l with
	    | (SMTLetVar _ as v)::t::rest ->
	      SMTLetBinding(v,t)::(foldHeadLst rest)
	    | x::rest -> 
	      x::foldHeadLst rest
	    | [] -> []
	in
	(foldHeadLst headExpLst) @ tailExp 
      | SexpLet -> 
	begin
	  let tailExp = extract_term tailStr in
	  let b,t = split_last tailExp in
	  [SMTLet(b,t)]
	end
      | SexpIntConst -> 
	let tailExp = extract_term tailStr in
	let c = Int64.of_string headStr in
	let term = SMTConstant(c) in
	term :: tailExp
      | SexpVar ->
	let tailExp = extract_term tailStr in
	let term = if is_cse_var headStr 
	  then SMTLetVar(headStr)
	  else SMTVar(smtVarFromString headStr) 
	in
	term :: tailExp
      | SexpRel -> 
	let tailExp = extract_term tailStr in
	let rel = headStr in
	[SMTRelation(rel,tailExp)]
      | SexpBoolConst -> 
	let tailExp = extract_term tailStr in
	if headStr = "true" then SMTTrue :: tailExp
	else if headStr = "false" then SMTFalse :: tailExp
	else failwith "neither true nor false???"

let clause_from_sexp 
    (sexp: string) 
    (ssaBefore: varSSAMap) 
    (ic : ifContextList)
    (ct : clauseType) 
    : clause = 
  match extract_term sexp with 
    | [t] -> make_clause t ssaBefore ic ct noTags (*DSN TODO No tags at this point*)
    | _ -> failwith ("should only get one term from the sexp: " ^ sexp)

let begins_with str header =
  let ls = length str in
  let lh = length header in
  if ls >= lh then
    let strHead = sub str 0 lh in
    strHead = header 
  else
    false



(*********************************C to smt converstion *************************************)
let formula_from_lval l = 
  match l with 
    | (Var(v),_) -> SMTVar(smtVarFromString(v.vname))
    | _ -> failwith "should only have lvals of type var"

(* IF YOU MODIFY this, you MUST modify smtUninterpreted and analyze_type *)
let smtOpFromBinop op = 
  match op with
    | PlusA | MinusA | Mult | Lt | Gt | Le | Ge ->  d_string "%a" d_binop op 
    | Div -> "div"
    | Mod -> "mod"
    | Eq -> "="
    | Ne -> "distinct"
    | LAnd -> "and"
    | LOr -> "or"
    (* Uninterpreted operators *)
    | BAnd ->  
      if not uninterpretedBitOperators then failwith "not supporting bit operators";
      "band" 
    | BXor -> 
      if not uninterpretedBitOperators then failwith "not supporting bit operators";
      "bxor"
    | BOr ->        
      if not uninterpretedBitOperators then failwith "not supporting bit operators";
      "bor"
    | Shiftlt -> 
      if not uninterpretedBitOperators then failwith "not supporting bit operators";
      "shiftlt"
    | Shiftrt -> 
      if not uninterpretedBitOperators then failwith "not supporting bit operators";
      "shiftrt"
    | _ -> failwith ("unexpected operator in smtopfrombinop |" 
		     ^ (d_string "%a" d_binop op ) ^ "|")

let smtUninterpreted = 
  ["band";
   "bxor";
   "bor";
   "shiftlt";
   "shiftrt";]


let rec formula_from_exp e = 
  match e with 
    | Const(CInt64(c,_,_)) -> SMTConstant(c)
    | Const(CChr(c)) -> SMTConstant(Int64.of_int (int_of_char c))
    | Const(_) -> failwith ("Constants should only be of type int: " ^ (d_string "%a" d_exp e))
    | Lval(l) -> formula_from_lval l 
    | UnOp(o,e1,t) -> 
      let opArg = d_string "%a" d_unop o in
      let eForm = formula_from_exp e1 in
      SMTRelation(opArg,[eForm])
    | BinOp(o,e1,e2,t) ->
      let opArg = smtOpFromBinop o in
      let eForm1 = formula_from_exp e1 in
      let eForm2 = formula_from_exp e2 in
      SMTRelation(opArg,[eForm1;eForm2])
    | CastE(t,e) -> formula_from_exp e
    | _ -> failwith ("not handelling this yet" ^ (d_string "%a" d_exp e))

let get_ssa_before () = 
  match !revProgram with
    | [] -> emptySSAMap
    | x::xs -> x.ssaIdxs


(****************************** Interpolation ******************************)
(* This is copied from the smtlib stuff in grasshopper.  Eventually, I should
 * really just port what I'm doing over to that.  But for now, I'll just take
 * the min necessary
 * https://subversive.cims.nyu.edu/thw/prototypes/grasshopper/src/smtlib/smtLibSolver.ml
 *)

type solver_kind = Process of string * string list

type solver_info = 
    { version: int;
      subversion: int;
      has_set_theory: bool;
      smt_options: (string * bool) list;
      kind: solver_kind; 
    }

let unsatCoreOptions =  
  ["print-success",false; "produce-proofs",true; "produce-unsat-cores", true]
let interpolationOptions = 
  ["print-success",false; "produce-proofs",true; "produce-unsat-cores", false]
let smtOnlyOptions = 
  ["print-success",false; "produce-proofs",false; "produce-unsat-cores", false]

let smtinterpol_2_1 = 
  let basedir = get_basedir () in
  let jarfile = basedir ^ "/smtinterpol/smtinterpol.jar" in
  { 
    version = 2; 
    subversion = 1;
    has_set_theory = false;
    smt_options = smtOnlyOptions;
    kind = Process("java",["-jar";jarfile;"-q"]);
  }
    
(* assume that z3 is on the path *)
let z3_4_3 = 
  { 
    version = 4; 
    subversion = 3;
    has_set_theory = false;
    smt_options = smtOnlyOptions;
    kind = Process("z3",["-smt2"; "-in"]);
  }


type solver = 
    { name : string;
      info : solver_info
    }

type solver_state = 
    { out_chan: out_channel;
      in_chan: in_channel;
      pid: int;
      log_out: out_channel option;
    }

let flush_solver solver = 
  flush solver.out_chan;
  match solver.log_out with 
    | Some logc -> flush logc
    | None -> ()

let write_line_to_solver solver line = 
  Printf.fprintf solver.out_chan "%s" line;
  match solver.log_out with 
    | Some logc -> Printf.fprintf logc "%s" line
    | None -> ()

let write_to_solver solver lines = 
  List.iter (write_line_to_solver solver) lines

let set_solver_options solver opts = 
  let set_option (opt_name,opt_value) =
    let optStr = Printf.sprintf "(set-option :%s %b)\n" opt_name opt_value in
    write_line_to_solver solver optStr
  in
  List.iter set_option opts

let set_timeout solver timeout = 
  write_line_to_solver solver ("(set-option :timeout " ^ string_of_int timeout ^ ")\n")

let set_logic solver logic = write_line_to_solver solver ("(set-logic " ^ logic ^ ")\n")
let declare_uninterpreted_ops solver ops = 
  if not uninterpretedBitOperators then failwith "not supporting bit operators";
  List.iter 
    (fun x -> write_line_to_solver solver ("(declare-fun " ^ x ^ " (Int Int) Int)\n"))
    ops
let declare_unknown_sort solver = write_line_to_solver solver "(define-sort Unknown () Int)\n"
  
let reset_solver solver = write_line_to_solver solver "(reset)\n"
let exit_solver solver = write_line_to_solver solver "(exit)\n"; flush_solver solver

let line_from_solver solver = 
  let line = input_line solver.in_chan in
  debug_endline line;
  line

let rec read_from_solver (solver) (pt) : smtResult =
  let l  = line_from_solver solver in
  if begins_with l "INFO" then 
    read_from_solver solver pt (*skip *)
  else if begins_with l "unsat" then 
    match pt with
      | CheckSat -> Unsat(GotNothing)
      | GetUnsatCore -> 
	let next_line = line_from_solver solver in
	let coreList = extract_unsat_core (next_line) in
	let coreSet = List.fold_left (fun a e -> StringSet.add e a) StringSet.empty coreList in
	Unsat(GotUnsatCore coreSet)
      | GetInterpolation _ -> 
	let next_line = line_from_solver solver in
	let terms = extract_term (next_line) in
	Unsat(GotInterpolant terms)
  else if begins_with l "sat" then
    Sat
  else if begins_with l "unknown" then
    Timeout
  else 
    failwith ("unmatched line:\n" ^ l ^ "\n")

(* Given a description of a solver, start the solver and create pipes to it *)
let start_with_solver session_name solver do_log = 
  let log_out = 
    if do_log then begin
      safe_mkdir smtDir 0o777;
      let log_file_name = smtDir ^ "/" ^ session_name ^ ".smt2" in
      Some(open_out log_file_name)
    end 
    else None
  in
  let state = match solver.info.kind with
    | Process (cmnd, args) ->
      let aargs = Array.of_list (cmnd :: args) in
      let in_read, in_write = Unix.pipe () in
      let out_read, out_write = Unix.pipe () in
      let pid = Unix.create_process cmnd aargs out_read in_write in_write in 
      { in_chan = Unix.in_channel_of_descr in_read;
	out_chan = Unix.out_channel_of_descr out_write;
	pid = pid;
	log_out = log_out;
      } in
  set_solver_options state solver.info.smt_options;
  set_timeout state 10000;
  state

let smtinterpolSolver = ref None
let getSmtinterpol () = match !smtinterpolSolver with
  | Some x -> x
  | None -> 
    let s = start_with_solver "smtinterpol_out" 
      {name = "smtinterpol"; info=smtinterpol_2_1} true in
    smtinterpolSolver := Some s;
    s

let z3Solver = ref None
let getZ3 () = match !z3Solver with
  | Some x -> x
  | None -> 
    let s = start_with_solver "z3_out" 
      {name = "z3"; info=z3_4_3} true in
    z3Solver := Some s;
    s


(* given a set of clauses, do what is necessary to turn it into smt queries *)
let _do_smt ?(justPrint = false) solver clauses pt =
  (* print_endline "doing smt"; *)
  reset_solver solver;
  let opts = match pt with 
    | CheckSat -> smtOnlyOptions
    | GetUnsatCore -> unsatCoreOptions 
    | GetInterpolation _-> interpolationOptions 
  in 
  set_solver_options solver opts;
  set_logic solver "QF_LIA";
  if uninterpretedBitOperators then declare_uninterpreted_ops solver smtUninterpreted;
  (* on occation, there are variables that are never used in a way where their type matters
   * assume they're ints *)
  declare_unknown_sort solver;
  (*write the declerations *)
  let allVars = all_vars clauses in
  VarSet.iter (fun v -> write_line_to_solver solver (make_var_decl v)) allVars;
  (* write the program clauses *)
  List.iter (fun x -> write_line_to_solver solver (!assertionStringFn x)) clauses;
  (* write the commands *)
  let cmds = match pt with
    | CheckSat -> 
      [smtCheckSat]
    | GetInterpolation (partition) ->  
      [smtCheckSat;partition]
    | GetUnsatCore -> 
      [smtCheckSat; smtGetUnsatCore]
  in
  write_to_solver solver cmds;
  flush_solver solver;
  if justPrint then NoSMTResult 
  else read_from_solver solver pt

let do_smt clauses pt =
  let solver = match pt with
    | CheckSat | GetUnsatCore -> getZ3 ()
    | GetInterpolation _ -> getSmtinterpol()
  in
  let res, duration = Dsnutils.time (fun () -> _do_smt solver clauses pt) () in
  smtCallTime := !smtCallTime @ [duration];
  debug_endline 
    ("No. calls=" ^ string_of_int (List.length !smtCallTime) 
     ^ ", Time_this=" ^ string_of_float duration
     ^ " Time_total=" ^ string_of_float (List.fold_left (+.) 0. !smtCallTime));
  res

let print_smt filenameOpt clauses pt = 
  match filenameOpt with
    | Some filename ->
      let oc = open_out (filename ^ ".smt2") in
      let solver = {
	in_chan = stdin;
	out_chan = oc;
	pid = 0;
	log_out = None} in
      ignore( _do_smt ~justPrint:true solver clauses pt);
      close_out oc;
    | None -> 
      let solver = {
	in_chan = stdin;
	out_chan = stdout;
	pid = 0;
	log_out = None;
      } in
      ignore(_do_smt ~justPrint:true solver clauses pt)


let are_interpolants_equiv (i1 :term) (i2 :term)= 
  (* interpolants have no need for ssa variables.  So we can just drop them *)
  let rec ssa_free_interpolant form = match form with
    | SMTLetBinding(v,e) -> SMTLetBinding(v,ssa_free_interpolant e)
    | SMTRelation(s,tl) -> SMTRelation(s,List.map ssa_free_interpolant tl)
    | SMTConstant(_) | SMTFalse | SMTTrue | SMTLetVar(_)-> form
    | SMTVar(v) -> SMTVar {v with ssaIdx=0}
    | SMTLet(b,t) -> SMTLet(List.map ssa_free_interpolant b,ssa_free_interpolant t)
  in
  let i1form = ssa_free_interpolant i1 in
  let i2form = ssa_free_interpolant i2 in
  if i1form = i2form then true 
  else 
    let equiv = SMTRelation("distinct",[i1form; i2form]) in
    let cls = make_clause equiv emptySSAMap emptyIfContext EqTest noTags in 
    match (do_smt [cls] CheckSat) with
      | Sat -> false
      | Unsat _ -> true
      | Timeout -> false (* conservative on timeout *)
      | NoSMTResult -> failwith "trying to get result from smt logging call"

let is_valid_interpolant (before :clause list) (after : clause list) (inter :clause) = 
  let not_inter = negate_clause inter in
  match do_smt (not_inter :: before) CheckSat  with
    | NoSMTResult -> failwith "trying to get result from smt logging call"
    | Timeout -> false
    | Sat -> false
    | Unsat(_) -> 
      match do_smt (inter :: after) CheckSat with
	| NoSMTResult -> failwith "trying to get result from smt logging call"
	| Sat -> false
	| Unsat(_) -> true 
	| Timeout -> false


(* requires that the interpolant be mapped into the ssa betweren before and after *)
let try_interpolant_forward_k k currentState interpolant suffix  =
  match split_off_n_reversed k suffix with
    | Some(leftRev,right) ->
      let lastLeft = List.hd leftRev in
      let interpolant = remap_clause lastLeft.ssaIdxs interpolant in
      if is_valid_interpolant (currentState::leftRev) right interpolant then begin
	InterpolantWorks(interpolant,right)
      end else begin
	InterpolantFails
      end
    | None -> NotKLeft
      
(* propegate as far forward as we can, until failure.  
 * if we were using k > 1, and failed, try again with k = 1
 * Then return the new interpolant
 * and the new right side *)
let rec propegate_interpolant_forward_linear k currentState interpolant suffix = 
  match try_interpolant_forward_k k currentState interpolant suffix with 
    | InterpolantWorks (interpolant,suffix) ->
      propegate_interpolant_forward_linear k interpolant interpolant suffix 
    | InterpolantFails -> 
      if k <= 1 then interpolant,suffix 
      else propegate_interpolant_forward_linear 1 currentState interpolant suffix
    | NotKLeft -> 
      if k <= 1 then failwith "was not expecting not k left with k = 1";
      propegate_interpolant_forward_linear 1 currentState interpolant suffix

let propegate_interpolant_binarysearch currentState interpolant suffix =
  let rec helper k currentState interpolant suffix = 
    if k = 0 then interpolant,suffix 
    else match try_interpolant_forward_k k currentState interpolant suffix with 
      | InterpolantWorks (interpolant,suffix) ->
	helper (k/2) interpolant interpolant suffix 
      | InterpolantFails -> 
	helper (k/2) interpolant interpolant suffix 
      | NotKLeft -> failwith "there really should be k left now"
  in
  (* try to go forward one,  If we can't then don't bother to do a binary search *)
  match try_interpolant_forward_k 2 currentState interpolant suffix with 
    | InterpolantWorks (interpolant,suffix) ->
      debug_endline "worked";
      helper (List.length suffix) currentState interpolant suffix
    | InterpolantFails  | NotKLeft -> 
      propegate_interpolant_forward_linear 1 currentState interpolant suffix

let reduce_trace_unsatcore (unreducedClauses : trace) : trace =
  match do_smt unreducedClauses GetUnsatCore with
    | Unsat (GotUnsatCore core) ->
      List.filter (fun c -> StringSet.mem (assertion_name c) core) unreducedClauses 
    | _-> failwith "unable to get core"
      
(* all this does is find the precondition for each statement.  No reductions *)
let make_cheap_annotated_trace (clauses : trace) : annotatedTrace = 
  let partition =  make_all_interpolants clauses in
  match do_smt clauses (GetInterpolation partition) with
    | Unsat (GotInterpolant inters) -> 
      (* the interpolant list will be missing the program precondition
       * so we start with an extra interpolant "true" *)
      let zipped = List.combine (SMTTrue::inters) clauses in
      zipped
    | _ -> failwith "make_cheap_annotated_trace failed"

let reduce_trace_noninductive (input : annotatedTrace) : annotatedTrace =
  let rec aux at accum = 
    match at with
      | (i1,s1)::(i2,s2)::rest -> 
	let _ , rhsClauses = List.split rest in
	let remapped = remap_formula s1.ssaIdxs i1 in
	let interpolant = make_clause remapped s1.ssaIdxs [] Interpolant noTags in
	let c1 =  make_clause i1 emptySSAMap  [] Interpolant noTags in
	if is_valid_interpolant [c1;s1] (s2::rhsClauses) interpolant then
	  aux ((remapped,s2)::rest) accum
	else 
	  aux ((i2,s2)::rest) ((i1,s1)::accum)
      | [x] -> x::accum
      | _ -> failwith "here"
  in
  List.rev (aux input [])

let propegate_forward_window (input : annotatedTrace) : annotatedTrace =
  let rec aux at accum = 
    match at with
      | (i1,s1)::(i2,s2)::(i3,s3)::rest -> 
	let remapped = remap_formula s1.ssaIdxs i1 in
	let interpolant = make_clause remapped s1.ssaIdxs [] Interpolant noTags in
	let c1 = make_clause i1 emptySSAMap   [] Interpolant noTags in
	let c3 =  make_clause i3 emptySSAMap   [] Interpolant noTags in
	if is_valid_interpolant [c1;s1][s2;c3] interpolant then
	  aux ((remapped,s2)::(i3,s3)::rest) accum
	else 
	  aux ((i2,s2)::(i3,s3)::rest) ((i1,s1)::accum)
      | _ -> accum
  in
  List.rev (aux input [])
    
(* reduced is the prefix of the trace *)
(* We will work as follows:
 * assume that the reducedPrefix is maximally reduced
 * At the end of this prefix, we are in the state currentState
 * We need the next assignment, otherwise we would have been able 
 * to map the interpolant even further forward
 * so take : [currentState; x ; prefix] and find an interpolant between
 * x and prefix.
 * map that as far as possible
 * repeat
 * keep the reduced prefix in reverse order to prevent unneccessary list conjunctions
 *)
let reduce_trace_expensive propAlgorithm trace = 
  let rec reduce_trace_imp reducedPrefixRev currentState unreducedSuffix =
    match unreducedSuffix with
      | [] -> reducedPrefixRev
      | [x] -> (currentState.formula,x)::reducedPrefixRev
      | x :: unreducedSuffix ->
	(* We know we need to keep x, but can we reduce the suffix further? *)
	let before = [currentState;x] in
	let after = unreducedSuffix in
	let partition = make_interpolate_between before after in
	match do_smt (before @ after) (GetInterpolation partition)  with 
	  | Unsat (GotInterpolant [interpolantTerm]) -> 
	    let interpolant = 
	      make_clause interpolantTerm x.ssaIdxs emptyIfContext Interpolant noTags in
	    (*find_farthest_point_interpolant_valid 
	     * we start in state interpolant, with guess 
	     * interpolant.  See if we can propegage it
	     * across the new suffix  *)
	    let newCurrentState, unreducedSuffix = 
	      propAlgorithm interpolant interpolant unreducedSuffix in
	    reduce_trace_imp 
	      ((currentState.formula,x)::reducedPrefixRev)
	      newCurrentState 
	      unreducedSuffix 
	  | Sat -> failwith "was sat"
	  | _ -> failwith "Problem getting interpolant"
  in
  List.rev (reduce_trace_imp [] (make_true_clause ()) trace)

let unsat_then_cheap trace =
  print_endline 
    ("started with " ^ string_of_int (List.length (reduced_linenums trace)) ^ " lines");
  let reduced = reduce_trace_unsatcore trace in
  print_endline 
    ("cheap left " ^ string_of_int (List.length (reduced_linenums reduced)) ^ " lines");
  make_cheap_annotated_trace reduced

let unsat_then_window trace = 
  let cheap = unsat_then_cheap trace in
  let window = propegate_forward_window cheap in
  debug_endline ("\n***** Finished with " ^ (string_of_int (List.length(reduced_linenums_at window))) ^ " loc *****\n\n");
  window

let unsat_then_noninductive trace = 
  let cheap = unsat_then_cheap trace in
  let noninductive = reduce_trace_noninductive cheap in
  debug_endline ("\n***** Finished with " 
		 ^ (string_of_int (List.length(reduced_linenums_at noninductive))) 
		 ^ " loc *****\n\n");
  noninductive

let unsat_then_expensive propAlgorithm trace = 
  debug_endline 
    ("started with " ^ string_of_int (List.length (reduced_linenums trace)) ^  " lines");
  let cheap = reduce_trace_unsatcore trace in
  debug_endline ("cheap left " ^ string_of_int(List.length(reduced_linenums cheap)) ^ " lines");
  (* Printf.printf "cheap left %d clauses\n" (List.length (cheap)); *)
  let expensive = reduce_trace_expensive propAlgorithm cheap in
  (* Printf.printf "expensive left %d lines\n" (List.length (reduced_linenums_at expensive)); *)
  (* Printf.printf "expensive left %d lines\n" (List.length (expensive)); *)
  debug_endline ("\n***** Finished with " ^ (string_of_int (List.length(reduced_linenums_at expensive))) ^ " loc *****\n\n");
  expensive
    

let extract_tid_opt cls = 
  let rec aux = function
    | [] -> None
    | x::xs ->  match x with
	| ThreadTag i -> Some i
	| _ -> aux xs
  in
  aux cls.cTags

let extract_tid cls = 
  match extract_tid_opt cls with
    | None -> failwith "no tid"
    | Some i -> i

let extract_group cls = 
  let rec aux = function
    | [] -> failwith "no tid"
    | x::xs ->  match x with
	| SummaryGroupTag i -> i
	| _ -> aux xs
  in
  aux cls.cTags

let contextswitches x = 
  let nums = List.map extract_tid_opt x in
  let nums = List.filter (fun c -> match c with | None -> false |Some _ ->true) nums in
  let nums = List.map (fun c -> match c with | None -> failwith "wtf" | Some i -> i) nums in
  compress nums

let contextswitches_at x = do_on_trace contextswitches x
let count_contextswitches x = List.length (contextswitches x) -1
let count_contextswitches_at x = List.length (contextswitches_at x) -1

let print_contextswitches description x =
  let cs = contextswitches x in
  let num = List.length cs - 1 in
  Printf.printf "%s\t(%d context switches)\t" description num;
  List.iter (Printf.printf "-%d-") cs;
  print_endline "";
  num

let print_contextswitches_at description x = 
  print_contextswitches description (trace_from_at x)

let count_statements clauses = 
  List.length 
    (List.filter (fun c -> match c.typ with ProgramStmt _ -> true | _ -> false) 
       clauses)

let count_statements_at at = do_on_trace count_statements at

let get_partition_interpolant partitionP trace =
  let partitionString = match List.partition partitionP trace with
    | (a,b) -> make_interpolate_between a b in
  let result = do_smt trace (GetInterpolation partitionString) in
  match result with 
    | Unsat(GotInterpolant [theInterpolant]) -> theInterpolant
    | _ -> failwith "didn't get interpolant for partition"
      
(* we can either work on tid or groups, by choosing the idExtractor function *)
let summerize_annotated_trace (idExtractor : clause -> int) 
    (fullTrace : annotatedTrace) (groupId : int) =
  let rec aux remaining groupAccum groupExitCond summaryAccum =
    match remaining with 
      | [] -> List.rev groupAccum
      | (i,c) as hd::xs -> begin
	match c.typ with 
	  | ProgramStmt(instr,Some thatTid) -> begin
	    let inGroup = (groupId = idExtractor c) in
	    match inGroup,groupExitCond with
	      | true,None -> 
		(* Were in desired thread, stayed in it*)
		aux xs (hd::groupAccum) None [] 
	      | true,Some cond  -> 
		(* we not in the desired group, now entered it.  Have to build 
		 * the summary *)
		let summary = make_clause 
		  (SMTRelation("=>",[cond;i])) 
		  c.ssaIdxs
		  emptyIfContext
		  (Summary(List.rev summaryAccum))
		  noTags 
		in
		aux xs (hd::(cond,summary)::groupAccum) None []
	      | false, None  -> 
		(* we just left the desired thread *)
		aux xs groupAccum (Some i) ((instr,Some thatTid)::summaryAccum)
	      | false, Some cond  -> 
		(* we are out of the desired thread, and have been for at least one statment*)
		aux xs groupAccum groupExitCond ((instr,Some thatTid)::summaryAccum)
	  end
	  | _ -> failwith "not a programstatment in summirization"
      end
  in
  aux fullTrace [] None []


(* we assume that the thread mentioned in the label is good until the next label
 * this requires that we use --keepunused to keep the labels active *)
let parseLabel s = 
  match s.labels with
    | [] -> ()
    | [Label(s,l,b)] -> begin
      if String.sub s 0 9 <> "VERMEER__" then
      match split_on_underscore s with
	| [prefix;tid;sid;group] ->
	  if prefix <> "T" then failwith ("invalid label prefix " ^ prefix);
	  let newThread = int_of_string tid in
	  let newGroup = int_of_string group in
	  seenThreads := TIDSet.add newThread !seenThreads;
	  currentThread := Some (newThread);
	  currentLabel := Some(s);
	  seenGroups := GroupSet.add newThread !seenThreads;
	  currentGroup := Some(newGroup)
	| _ -> failwith ("bad label string " ^ s)
    end
    | _ -> failwith ("unexpected label " ^ d_labels s.labels)

class dsnsmtVisitorClass = object
  inherit nopCilVisitor

  method vinst i = begin
    let tags = match !currentThread with
      | Some (tid) -> [ThreadTag tid]
      | None -> [] in
    let tags = match !currentLabel with
      | Some l -> (LabelTag l)::tags
      | None -> tags in
    let tags = match !currentGroup with
      | Some g -> SummaryGroupTag g :: tags
      | None -> tags in
    let ssaBefore = get_ssa_before() in
    match i with
      |  Set(lv, e, l) -> 
	let lvForm = formula_from_lval lv in
	let eForm = formula_from_exp e in
	let assgt = SMTRelation("=",[lvForm;eForm]) in
	let cls = make_clause assgt ssaBefore !currentIfContext (ProgramStmt (i,!currentThread)) tags in
	revProgram := cls :: !revProgram;
	DoChildren
      | Call(lo,e,al,l) ->
	assert_is_assert i;
	let form = match al with 
	  | [x] -> formula_from_exp x
	  | _ -> failwith "assert should have exactly one element"
	in
	let cls = make_clause form ssaBefore !currentIfContext (ProgramStmt (i,!currentThread)) tags in
	revProgram := cls :: !revProgram;
	DoChildren
      | _ -> DoChildren
  end
  method vstmt (s : stmt) = begin
    parseLabel s;
    match s.skind with
      | If(i,t,e,l) ->
	if e.bstmts <> [] then failwith "else block not handeled";
	let cond = type_check_and_cast_to_bool (formula_from_exp i) in
	currentIfContext := {iformula = cond; istmt = s} :: !currentIfContext;
	ChangeDoChildrenPost (s,
			      fun x -> 
				currentIfContext := List.tl !currentIfContext;
				x)
      | Block _ -> DoChildren
      | _ -> DoChildren
  end
end

let dsnsmtVisitor = new dsnsmtVisitorClass

let reduce_using_technique technique clauses  = 
  match technique with 
    | UNSATCORE -> unsat_then_cheap clauses
    | LINEARSEARCH -> unsat_then_expensive (propegate_interpolant_forward_linear 1) clauses 
    | BINARYSEARCH -> unsat_then_expensive (propegate_interpolant_binarysearch) clauses 
    | WINDOW -> unsat_then_window clauses
    | NONINDUCTIVE -> unsat_then_noninductive clauses
    | NOREDUCTION -> make_cheap_annotated_trace clauses

let calculate_stats (description : string) (trace : clause list)  = 
  let switches = count_contextswitches trace in
  let stmts = count_statements trace in
  let numvars = count_basevars trace in
  Printf.printf "%s\tSwitches: %d\tStmts: %d\tVars: %d\n"
    description switches stmts numvars

let calculate_thread_stats (trace : clause list) = 
  TIDSet.iter (fun tid -> 
    let tidStmts = List.filter 
      (fun c -> match c.typ with | ProgramStmt _ -> (extract_tid c) = tid | _ -> false) trace in
    calculate_stats ("Init" ^ string_of_int tid) tidStmts ) !seenThreads
    
let calculate_stats_at description at = calculate_stats description (trace_from_at at)

let annotated_trace_to_smtfile at filename = 
  let interpolants,trace = List.split at in
  print_smt (Some filename) trace CheckSat 
    
let reduce_to_file technique filename clauses =
  let reduced = reduce_using_technique technique clauses in
  calculate_stats_at "Reduced" reduced;
  print_annotated_trace_to_file filename reduced;
  if(!printReducedSMT) then 
    annotated_trace_to_smtfile reduced filename;
  reduced

let summarize_to_file technique reduced id = 
  let summarized = summerize_annotated_trace technique reduced id  in
  calculate_stats_at ("Slice" ^ string_of_int id) summarized;
  print_annotated_trace_to_file ("summary" ^ string_of_int id) summarized
    
let partition_to_file technique reduced id = 
  print_endline ("Partitioning. A group is " ^ string_of_int id);
  let interpolant = get_partition_interpolant 
    (fun x -> (technique x) = id) reduced in
  print_endline (string_of_formula interpolant)

let dsnsmt (f: file) : unit =
  let doGlobal = function 
    | GVarDecl (v, _) -> ()
    | GFun (fdec, loc) ->
      currentFunc := fdec.svar.vname;
      (* do the body *)
      ignore (visitCilFunction dsnsmtVisitor fdec);
    | _ -> () in 
  let _ = Stats.time "dsn" (iterGlobals f) doGlobal in
  let clauses = List.rev !revProgram in
  (* add a true assertion at the begining of the program *)
  let clauses = make_true_clause () :: clauses in
  calculate_stats "Initial" clauses;
  if !printTraceSMT then print_smt (Some "fulltrace") clauses CheckSat;
  begin match !multithread with
    | PARTITIONTID -> 
      let reducedClauses = reduce_trace_unsatcore clauses in
      TIDSet.iter (partition_to_file extract_tid reducedClauses) !seenThreads
    | PARTITIONGROUP -> 
      let reducedClauses = reduce_trace_unsatcore clauses in
      GroupSet.iter (partition_to_file extract_group reducedClauses) !seenGroups
    | ALLGROUPS -> 
      let reduced = reduce_to_file !analysis "reduced" clauses in
      GroupSet.iter (summarize_to_file extract_group reduced) !seenGroups
    | ALLTHREADS ->
      let reduced = reduce_to_file !analysis "reduced" clauses in
      calculate_thread_stats clauses;
      TIDSet.iter (summarize_to_file extract_tid reduced) !seenThreads
    | ABSTRACTENV -> 
      TIDSet.iter 
	(fun tid  -> 
	  print_string ("\n\n***Processing abstract thread: " ^ string_of_int tid);
	  assertionStringFn := make_abstract_env_assertion_string tid;
	  let reduced = reduce_to_file 
	    !analysis ("reduced" ^ string_of_int tid) clauses in
	  summarize_to_file extract_tid reduced tid 
	) 
	!seenThreads
    | NOMULTI -> 
      ignore(reduce_to_file !analysis "smtresult" clauses)
  end ;
  (*this is slightly inefficient: if the solver has not been started,
   * this will start it and then exit it *)
  exit_solver (getZ3());
  exit_solver (getSmtinterpol())
	

let feature : featureDescr = 
  { fd_name = "dsnsmt";
    fd_enabled = Cilutil.dsnSmt;
    fd_description = "Converts linearized concrete c program to SMT";
    fd_extraopt = 
      [ ("--runsmtanalysistype", 
	 Arg.String 
	   (fun x -> match x with 
	     | "noreduction" -> analysis := NOREDUCTION
	     | "unsatcore" -> analysis := UNSATCORE
	     | "linearsearch" -> analysis := LINEARSEARCH
	     | "binarysearch" -> analysis := BINARYSEARCH
	     | "window" -> analysis := WINDOW
	     | "noninductive" -> analysis := NONINDUCTIVE
	     | x -> failwith (x ^ " is not a valid analysis type")),
	 " the analysis to use unsatcore linearsearch binarysearch");
	("--smtdebug", Arg.Unit (fun x -> debugLevel := 2), 
	 " turns on printing debug messages");
	("--smtprinttrace", Arg.Unit (fun x -> printTraceSMT := true), 
	 " prints the origional trace to smt");
	("--smtprintreduced", Arg.Unit (fun x -> printReducedSMT := true), 
	 " prints the reduced code to smt");
	("--smtmultithread", Arg.String 
	  (fun x -> match x with
	    | "partitionTID" -> multithread := PARTITIONTID
	    | "partitionGroup" -> multithread := PARTITIONGROUP
	    | "allgroups" -> multithread := ALLGROUPS
	    | "allthreads" -> multithread := ALLTHREADS
	    | "abstractenv" -> multithread := ABSTRACTENV
	    | "nomulti" -> multithread := NOMULTI
	    | x -> failwith (x ^ " is not a valid multithread analysis type")), 
	 " turns on multithreaded analysis");
      ];
    fd_doit = dsnsmt;
    fd_post_check = true
  } 

