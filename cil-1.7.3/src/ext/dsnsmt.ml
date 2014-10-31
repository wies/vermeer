(* TODOS
 * fix Int vs Bool problem - DONE
 * handle conditions from if statements - DONE?
 * handle operators that differ between c and smt eg && vs and
 * remap interpolants when returning them
 *)

open Cil

(* issue if interpolant tries to go past where something is used *)

open String
open Printf
(* consider using https://realworldocaml.org/v1/en/html/data-serialization-with-s-expressions.html *)

(******************************** Optimizations ***************************)
(* keep around the vars for a partition
 *)

(*******************************TYPES *************************************)


module Int = struct                       
  type t = int                                              
  let compare x y = if x < y then -1 else if x > y then 1 else 0 end ;;  

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
type varSSAMap = smtvar VarSSAMap.t
type varTypeMap = smtVarType TypeMap.t
let emptySSAMap : varSSAMap = VarSSAMap.empty
let emptyTypeMap : varTypeMap = TypeMap.empty
let emptyVarSet = VarSet.empty
let emptyStringSet = StringSet.empty

type term = | SMTRelation of string * term list
	    | SMTConstant of int64
	    | SMTVar of smtvar 
	    | SMTTrue | SMTFalse


(* TODO record the program location in the programStmt *)
type clauseType = ProgramStmt of Cil.instr | Interpolant | Constant | EqTest

type sexpType = Sexp | SexpRel | SexpIntConst | SexpVar | SexpBoolConst

type clause = {formula : term; 
	       idx : int; 
	       vars : VarSet.t; 
	       ssaIdxs : varSSAMap;
	       typ : clauseType;
	       ifContext : term list
	      }

type trace = clause list
type annotatedTrace = (term * clause) list
(* we take the left hand side of the interpolation problem 
 * this lets us have the info we need for remapping vars etc
 *)
type problemType = CheckSat | GetInterpolation of string | GetUnsatCore
type unsatResult = GotInterpolant of term list | GotUnsatCore of StringSet.t | GotNothing
type smtResult = Sat | Unsat of unsatResult
type forwardProp = InterpolantWorks of clause * clause list | NotKLeft | InterpolantFails
type ifContext = term list

exception CantMap of smtvar


(******************** Defs *************************)
let smtDir = "./smt/"
let smtCheckSat = "(check-sat)\n"
let smtGetUnsatCore = "(get-unsat-core)\n"

let smtZero = SMTConstant(0L)
let emptyIfContext = []

(******************** Globals *************************)
let count = ref 1
let currentFunc: string ref = ref ""
(*keep the program in reverse order, then flip once. Avoid unneccessary list creation*)
let revProgram : clause list ref = ref [] 
let typeMap : varTypeMap ref  = ref emptyTypeMap
let currentIfContext : ifContext ref = ref emptyIfContext
let flowSensitiveEncoding = true

(************************* utils *************************)
let time f x =
  let start = Unix.gettimeofday ()
  in let res = f x
     in let stop = Unix.gettimeofday ()
	in let () = Printf.printf "Execution time: %fs\n%!" (stop -. start)
	   in
	   flush stdout; res

let print_bars msg str = print_string (msg ^ " |" ^ str ^"|\n")

let rec sublist b e l = 
  match l with
      [] -> failwith "sublist"
    | h :: t -> 
      let tail = if e=0 then [] else sublist (b-1) (e-1) t in
      if b>0 then tail else h :: tail

(* returns the list split in two.  The left hand side is reversed *)
let split_off_n_reversed n l = 
  let rec helper n l leftAcc = 
    if n <= 0 then Some(leftAcc,l)
    else 
      match l with 
	|	[] -> None
	| x::xs -> helper (n-1) xs (x::leftAcc) 
  in
  helper n l [] 

let rec last = function
  | [] -> None
  | [x] -> Some x
  | _ :: t -> last t;;

let rec all_but_last lst = 
  List.rev  (List.tl (List.rev lst))

let d_string (fmt : ('a,unit,Pretty.doc,string) format4) : 'a = 
  let f (d: Pretty.doc) : string = 
    Pretty.sprint 800 d
  in
  Pretty.gprintf f fmt 

let safe_mkdir name mask = 
  if not (Sys.file_exists name) then Unix.mkdir name mask

(****************************** Clauses ******************************)
(* two possibilities: either maintain a mapping at each point
 * or remap as we go starting from one end *)


(* So we need to figure out the type of each variable *)
let get_var_type (var : smtvar) : smtVarType = 
  try IntMap.find var.vidx !typeMap 
  with Not_found -> SMTUnknown


(* this function does two things: It determines the type of the 
 * expression.  It also updates the mapping with any newly discovered
 * var -> type mappings
 *)

let string_of_vartype typ = 
  match typ with
    |SMTInt -> "Int"
    |SMTBool -> "Bool"
    |SMTUnknown -> "Unknown"

let analyze_var_type (topForm : term) =
  let types_match t1 t2 =
    match t1,t2 with
      | SMTUnknown,_ | SMTInt,SMTInt | SMTBool,SMTBool -> true
      | _ -> false
  in
  let second_if_matching t1 t2 = 
    if types_match t1 t2 then t2 else raise (Failure "mismatching types")
  in
  let update_type (var : smtvar) newType = 
    let currentType = get_var_type var  in
    match (currentType,newType) with 
      | (_, SMTUnknown) -> currentType
      | (SMTUnknown,_) -> 
	typeMap := TypeMap.add var.vidx newType !typeMap;
	newType
      | _ when (currentType = newType)-> 
	newType
      | _ -> 
	raise (Failure ("mismatching types " ^ var.fullname ^ " " ^ 
			   (string_of_vartype currentType) ^ " " ^
			   (string_of_vartype newType)))
  in
  let rec analyze_type_list typ tl  = 
    match tl with 
      | [] -> typ
      | x::xs -> 
	let updatedTyp = analyze_type typ x in
	if types_match typ updatedTyp then 
	  analyze_type_list updatedTyp xs
	else raise (Failure "types don't match")
  and analyze_type typ f = 
    match f with 
      | SMTFalse | SMTTrue -> second_if_matching typ SMTBool
      | SMTConstant(_) -> second_if_matching typ SMTInt
      | SMTVar(v) -> update_type v typ
      | SMTRelation(s,l) -> begin
	match s with 
	  | "<" | ">" | "<=" | ">=" -> (*int list -> bool *)
	    let _  = analyze_type_list SMTInt l in (*first update the children*)
	    second_if_matching typ SMTBool
	  | "and" | "or" | "xor" | "not" -> (*bool list -> bool*)
	    let _ = analyze_type_list SMTBool l in
	    second_if_matching typ SMTBool
	  | "ite" -> 
	    (* we analyze the list twice.  Once to find out what kind it is
	     * the second time to propegate that result to everything in it 
	     * The type of an ite is the type of its list
	     *)
	    let t1 = analyze_type_list SMTUnknown l in
	    let t2 = second_if_matching t1 (analyze_type_list t1 l) in
	    second_if_matching typ t2
	  | "=" | "distinct" ->
	    (* we analyze the list twice.  Once to find out what kind it is
	     * the second time to propegate that result to everything in it 
	     *)
	    let t1 = analyze_type_list SMTUnknown l in
	    let _ = second_if_matching t1 (analyze_type_list t1 l) in
	    second_if_matching typ SMTBool
	  | "+" | "-" | "*" | "div" | "mod" | "abs" -> 
	    let _ = analyze_type_list SMTInt l in
	    second_if_matching typ SMTInt
	  | _ -> raise (Failure ("unexpected operator in analyze type |" ^ s ^ "|"))
      end
  in
  analyze_type SMTUnknown topForm

(* not tail recursive *)
let rec get_vars formulaList set = 
  match formulaList with 
    | [] -> set
    | x::xs ->
      let set = get_vars xs set in
      match x with
	| SMTRelation(s,l) -> get_vars l set
	| SMTConstant(_) | SMTFalse | SMTTrue -> set
	| SMTVar(v) -> VarSet.add v set 
	  
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

let make_clause (f: term) (ssa: varSSAMap) (ic : ifContext)  (ct: clauseType)
    : clause = 
  incr count;
  let v  = get_vars [f] emptyVarSet in
  let ssa  = make_ssa_map (VarSet.elements v) ssa in
  let _ = analyze_var_type f in (* update the typemap to include this clause *)
  let c  = {formula = f; idx = !count; vars = v; ssaIdxs = ssa; typ = ct; ifContext = ic} in
  c

let make_true_clause () = make_clause SMTTrue emptySSAMap emptyIfContext Constant
let make_false_clause () =  make_clause SMTFalse emptySSAMap emptyIfContext Constant

let negate_clause cls = 
  {formula = SMTRelation("not",[cls.formula]);
   idx = cls.idx;
   vars = cls.vars;
   ssaIdxs = cls.ssaIdxs;
   typ = cls.typ;
   ifContext = cls.ifContext
  }

(****************************** Remapping ******************************)
(* TODO need to decide what to do if there is no mapping i.e. we've gone 
 * before the first def.  Options include 
 * throw an exception
 * let it be havoced i.e. have a blank 0 mapping for all vars
 *)

let get_current_var oldVar ssaMap = 
  try Some (VarSSAMap.find oldVar.vidx ssaMap)
  with Not_found -> None

let rec remap_formula ssaMap form =
  match form with
    | SMTRelation(s,tl) ->
      let lst = List.map (remap_formula ssaMap) tl in
      SMTRelation(s,lst)
    | SMTConstant(_) | SMTFalse | SMTTrue -> form
    | SMTVar(v) ->
      let newVarOpt = get_current_var v ssaMap in
      match newVarOpt with
	| Some (newVar) -> SMTVar(newVar)
	| None -> raise (CantMap v)

	  

(* I guess we should remap the if context too.  Does this make sense? 
 * Also, there is a bug where we ended up with two clauses with the same interpolation
 * id.  Make a new clause with a new id
 * possibly just assert that the if context is empty
 *)
let remap_clause ssaMap cls = 
  make_clause 
    (remap_formula ssaMap cls.formula) 
    ssaMap 
    (List.map (remap_formula ssaMap) cls.ifContext)
    cls.typ    

(******************** Print Functions *************************)
let string_of_var v = v.fullname

let rec string_of_args a = 
  match a with
    | [] -> ""
    | arg :: args -> (string_of_formula arg) ^ " " ^ (string_of_args args)

and string_of_formula f = 
  match f with
    | SMTRelation(rel, args) -> 
      "(" ^ rel ^ " " ^(string_of_args args) ^ ")"
    | SMTConstant(i) -> Int64.to_string i
    | SMTVar(v) -> string_of_var v
    | SMTFalse -> "false"
    | SMTTrue -> "true"
let string_of_term = string_of_formula

let string_of_clause c = 
  string_of_formula c.formula

let string_of_cprogram c =
  match c.typ with 
    | ProgramStmt i -> d_string "%a" d_instr i
    | Interpolant | Constant -> "//" ^ string_of_formula c.formula
    | EqTest -> raise (Failure "shouldn't have equality tests in the final program")

let string_of_cl cl = List.fold_left (fun a e -> a ^ string_of_clause e ^ "\n") "" cl

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
    | SMTRelation(rel, args) -> 
      "\t(" ^ "Rel: " ^ rel ^ " args: " ^(debug_args args) ^ ")"
    | SMTConstant(i) -> Int64.to_string i
    | SMTVar(v) -> debug_var v
    | SMTFalse | SMTTrue -> string_of_formula f

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
  match c.typ with
    | ProgramStmt(_) -> "PS_" ^ (string_of_int c.idx)
    | Interpolant -> "IP_" ^ (string_of_int c.idx)
    | Constant -> "CON_" ^ (string_of_int c.idx)
    | EqTest -> "EQTEST_" ^ (string_of_int c.idx)

let make_assertion_string c =
  let make_ifContext_formula ic = 
    match ic with 
      | [] -> SMTTrue
      | [x] -> x
      | _ -> SMTRelation("and",ic)
  in
  let form = 
    if flowSensitiveEncoding && c.ifContext <> [] then
      SMTRelation("=>", 
		  [make_ifContext_formula c.ifContext; 
		   c.formula])
    else c.formula in 
  "(assert (! " 
  ^ string_of_formula form
  ^ " :named " ^ assertion_name c
  ^ "))\n"
    
let make_var_decl v =
  let ts = string_of_vartype (get_var_type v) in
  "(declare-fun " ^ (string_of_var v)  ^" () " ^ ts ^ ")\n" 

let print_formulas x = 
  List.iter (fun f -> Printf.printf "%s\n" (string_of_formula f)) x; 
  flush stdout
let print_clauses x = 
  List.iter (fun f -> Printf.printf "%s\n" (string_of_clause f)) x; 
  flush stdout
let print_cprogram x = 
  List.iter (fun f -> Printf.printf "%s\n" (string_of_cprogram f)) x; 
  flush stdout
let print_annotated_trace x = 
  List.iter (fun (t,c) -> Printf.printf "%s\n\t%s\n" (string_of_formula t)
    (string_of_clause c)) x; 
  flush stdout

(******************** File creation ********************)

let make_all_interpolants program =
  let str = List.fold_left (fun accum elem -> accum ^ " " ^ (assertion_name elem)) "" program in
  "(get-interpolants " ^ str ^ ")\n"

    
let make_interpolate_between before after = 
  let string_of_partition part = 
    match part with 
      | [] -> raise (Failure "should be a partition")
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
	|  "and" | "distinct" | "or" | "not" | "xor" 
	  -> SexpRel
	| "false" | "true" 
	  -> SexpBoolConst
	| _
	  -> SexpVar
      end

let split_on_underscore str = Str.split (Str.regexp "[_]+") str

(* canonical format: x_vidx_ssaidx *)
let smtVarFromString str = 
  match split_on_underscore str with
    | [prefix;vidxStr;ssaIdxStr] -> 
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

let rec extract_unsat_core (str) : string list = 
  let str = strip_parens str in
  Str.split (Str.regexp "[ \t]+") str

let rec extract_term (str) : term list = 
  (* returns the first sexp as a string,
   * and the remainder as another string *)
  let extract_first_sexp str = 
    let str = trim str in
    let len = length str in
    if len = 0 then
      raise (Failure "nothing here") 
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
  let str = trim str in
  let str = strip_parens str in
  if length str = 0 then 
    []
  else
    let headStr, tailStr = extract_first_sexp str in
    let tailExp = extract_term tailStr in
    match getFirstArgType headStr with
      | Sexp -> 
	let headExpLst = extract_term headStr in
	if (List.length headExpLst) = 1 then
	  headExpLst @ tailExp
	else
	  raise (Failure ("headExpList had unexpected length: " ^ string_of_int(List.length headExpLst)))
      | SexpIntConst -> 
	let c = Int64.of_string headStr in
	let term = SMTConstant(c) in
	term :: tailExp
      | SexpVar ->
	let v = smtVarFromString headStr in
	let term = SMTVar(v) in
	term :: tailExp
      | SexpRel -> 
	let rel = headStr in
	let term = SMTRelation(rel,tailExp) in
	[term]
      | SexpBoolConst -> 
	if headStr = "true" then SMTTrue :: tailExp
	else if headStr = "false" then SMTFalse :: tailExp
	else raise (Failure "neither true nor false???")

let clause_from_sexp (sexp: string) (ssaBefore: varSSAMap) (ic : ifContext)(ct : clauseType) 
    : clause = 
  match extract_term sexp with 
    | [t] -> make_clause t ssaBefore ic ct
    | _ -> raise (Failure ("should only get one term from the sexp: " ^ sexp))

let begins_with str header =
  let ls = length str in
  let lh = length header in
  if ls >= lh then
    let strHead = sub str 0 lh in
    strHead = header 
  else
    false

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

let smtinterpol_2_1 = 
  { 
    version = 2; 
    subversion = 1;
    has_set_theory = false;
    smt_options = ["print-success",false; "produce-proofs",true; "produce-unsat-cores", true];
    kind = Process("java",["-jar";"/home/dsn/sw/smtinterpol/smtinterpol.jar";"-q"]);
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

let set_option solver (opt_name,opt_value) =
  let optStr = Printf.sprintf "(set-option :%s %b)\n" opt_name opt_value in
  write_line_to_solver solver optStr

let set_logic solver logic = write_line_to_solver solver ("(set-logic " ^ logic ^ ")\n")
let reset_solver solver = write_line_to_solver solver "(reset)\n"
let exit_solver solver = write_line_to_solver solver "(exit)\n"; flush_solver solver

let rec read_from_solver (solver) (pt) : smtResult =
  let l  = input_line solver.in_chan in
  if begins_with l "INFO" then 
    read_from_solver solver pt (*skip *)
  else if begins_with l "unsat" then 
    match pt with
      | CheckSat -> Unsat(GotNothing)
      | GetUnsatCore -> 
	let next_line = input_line solver.in_chan in
	let coreList = extract_unsat_core (next_line) in
	let coreSet = List.fold_left (fun a e -> StringSet.add e a) StringSet.empty coreList in
	Unsat(GotUnsatCore coreSet)
      | GetInterpolation _ -> 
	let next_line = input_line solver.in_chan in
	let terms = extract_term (next_line) in
	Unsat(GotInterpolant terms)
  else if begins_with l "sat" then
    Sat
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
  List.iter (set_option state) solver.info.smt_options;
  state

let singleSolver = start_with_solver "single_solver" 
  {name = "single_solver"; info=smtinterpol_2_1} true

(* given a set of clauses, do what is necessary to turn it into smt queries *)
let do_smt clauses pt =
  let solver = singleSolver in

  reset_solver solver;
  set_logic solver "QF_LIA";
  (*write the declerations *)
  let allVars = List.fold_left (fun a e -> VarSet.union e.vars a) emptyVarSet clauses in
  VarSet.iter (fun v -> write_line_to_solver solver (make_var_decl v)) allVars;
  (* write the program clauses *)
  List.iter (fun x -> write_line_to_solver solver (make_assertion_string x)) clauses;
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
  read_from_solver solver pt

let are_interpolants_equiv (i1 :term) (i2 :term)= 
  (* interpolants have no need for ssa variables.  So we can just drop them *)
  let rec ssa_free_interpolant form = match form with
    | SMTRelation(s,tl) ->SMTRelation(s,List.map ssa_free_interpolant tl)
    | SMTConstant(_) | SMTFalse | SMTTrue -> form
    | SMTVar(v) -> SMTVar {fullname=v.fullname;vidx=v.vidx;owner=v.owner;ssaIdx=0}
  in
  let i1form = ssa_free_interpolant i1 in
  let i2form = ssa_free_interpolant i2 in
  if i1form = i2form then true 
  else 
    let equiv = SMTRelation("distinct",[i1form; i2form]) in
    let cls = make_clause equiv emptySSAMap emptyIfContext EqTest in
    match (do_smt [cls] CheckSat) with
      | Sat -> false
      | Unsat _ -> true

(* requires that the interpolant be mapped into the ssa betweren before and after *)

let try_interpolant_forward_k k currentState interpolant suffix  =
  let is_valid_interpolant (before :clause list) (after : clause list) (inter :clause) = 
    let not_inter = negate_clause inter in
    match do_smt (not_inter :: before) CheckSat  with
      | Sat -> false
      | Unsat(_) -> 
	match do_smt (inter :: after) CheckSat with
	  | Sat -> false
	  | Unsat(_) -> true 
  in
  match split_off_n_reversed k suffix with
    | Some(leftRev,right) ->
      let lastLeft = List.hd leftRev in
      let interpolant = remap_clause lastLeft.ssaIdxs interpolant in
      if is_valid_interpolant (currentState::leftRev) right interpolant then
	InterpolantWorks(interpolant,right)
      else 
	InterpolantFails
    | None -> NotKLeft
      
let rec propegate_interpolant_forward_linear k currentState interpolant suffix = 
  match try_interpolant_forward_k k currentState interpolant suffix with 
    | InterpolantWorks (interpolant,suffix) ->
      propegate_interpolant_forward_linear k interpolant interpolant suffix 
    | InterpolantFails -> 
      if k <= 1 then interpolant,suffix 
      else propegate_interpolant_forward_linear 1 currentState interpolant suffix
    | NotKLeft -> propegate_interpolant_forward_linear 1 currentState interpolant suffix

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
  helper (List.length suffix) currentState interpolant suffix

(* this may subsume the reduce_trace_cheap! *)
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

let reduce_trace_cheap (unreducedClauses : trace) : annotatedTrace =
  (* Given an annotated list [I1,S1; I2,S2, etc) 
   * such that I1 is the precondition for S1. (ie the program goes I1 S1 I2 S2 ...
   * if I1 and I2 are identical, then S1 is unnecessary.
   *)
  let rec propegate_forward_cheap (input : annotatedTrace) : annotatedTrace  =
    match input with 
      | [] | [_] -> input
      | (i1,c1)::((i2,c2)::_ as rest)  -> 
	if are_interpolants_equiv i1 i2 then begin
	  (* if we match, we can throw away the next statement, and continue *)
	  propegate_forward_cheap rest end
	else (* if we didn't match, we need to hold on to the old startc *)
	  input 
  in
  let rec propegate_cheap_driver  (input : annotatedTrace) (revAccum : annotatedTrace) 
      : annotatedTrace = 
    match propegate_forward_cheap input with
      | [] -> List.rev revAccum
      | x::xs -> 
	let revAccum = x::revAccum in
	propegate_cheap_driver xs revAccum
  in
  let unreducedTrace = make_cheap_annotated_trace unreducedClauses in
  propegate_cheap_driver unreducedTrace [] 

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
      | [x] -> x:: reducedPrefixRev
      | x :: xs ->
	let clist = currentState :: unreducedSuffix in
	let before = [currentState;x] in
	let after = xs in
	let partition = make_interpolate_between before after in
	match do_smt clist (GetInterpolation partition)  with 
	  | Unsat (GotInterpolant [interpolantTerm]) -> 
	    let interpolant = make_clause interpolantTerm x.ssaIdxs emptyIfContext Interpolant in
	    let newCurrentState, unreducedSuffix = 
	      (*find_farthest_point_interpolant_valid *)
	      propAlgorithm currentState interpolant unreducedSuffix in
	    reduce_trace_imp 
	      (x::currentState::reducedPrefixRev)
	      newCurrentState
	      unreducedSuffix
	  | Sat -> failwith "was sat"
	  | _ -> failwith "Problem getting interpolant"
  in
  List.rev (reduce_trace_imp [] (make_true_clause ()) trace)

let cheap_then_expensive propAlgorithm trace = 
  let cheap = reduce_trace_cheap trace in
  let forms,clauses = List.split cheap in
  let expensive = reduce_trace_expensive propAlgorithm clauses in
  expensive

(*********************************C to smt converstion *************************************)
let rec formula_from_lval l = 
  match l with 
    | (Var(v),_) -> SMTVar(smtVarFromString(v.vname))
    | _ -> failwith "should only have lvals of type var"

(*DSN TODO check if there are any differences in cilly vs smt opstrings *)
let smtOpFromBinop op = 
  match op with
    | PlusA | MinusA | Mult | Lt | Gt | Le | Ge ->  d_string "%a" d_binop op 
    | Div -> "div"
    | Mod -> "mod"
    | Eq -> "="
    | Ne -> "distinct"
    | LAnd -> "and"
    | LOr -> "or"
    | _ -> failwith ("unexpected operator in smtopfrombinop |" 
		     ^ (d_string "%a" d_binop op ) ^ "|")

let rec formula_from_exp e = 
  match e with 
    | Const(CInt64(c,_,_)) -> SMTConstant(c)
    | Const(_) -> raise (Failure "Constants should only be of type int")
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

let make_bool f = 
  match analyze_var_type f with
    | SMTBool -> f
    | SMTInt -> SMTRelation("distinct",[f;smtZero])
    | SMTUnknown -> raise (Failure ("assertion is neither bool not int: " ^ 
				       (debug_formula f) ^
				       (debug_typemap())))
      

      
class dsnsmtVisitorClass = object
  inherit nopCilVisitor

  method vinst i = begin
    match i with
      |  Set(lv, e, l) -> 
	let lvForm = formula_from_lval lv in
	let eForm = formula_from_exp e in
	let assgt = SMTRelation("=",[lvForm;eForm]) in
	let ssaBefore = get_ssa_before() in
	let cls = make_clause assgt ssaBefore !currentIfContext (ProgramStmt i) in
	revProgram := cls :: !revProgram;
	DoChildren
      | Call(lo,e,al,l) ->
	let fname = d_string "%a" d_exp e in
	if fname <> "assert" then raise (Failure "shouldn't have calls in a concrete trace");
	let form = match al with 
	  | [x] -> formula_from_exp x
	  | _ ->  raise (Failure "assert should have exactly one element") 
	in
	let form = make_bool form in 
	let ssaBefore = get_ssa_before() in
	let cls = make_clause form ssaBefore !currentIfContext (ProgramStmt i) in
	revProgram := cls :: !revProgram;
	DoChildren
      | _ -> DoChildren
  end
  method vstmt (s : stmt) = begin
    match s.skind with
      | If(i,t,e,l) ->
	if e.bstmts <> [] then raise (Failure "else block not handeled");
	let cond = make_bool (formula_from_exp i) in
	currentIfContext := cond :: !currentIfContext;
	ChangeDoChildrenPost (s,
			      fun x -> 
				currentIfContext := List.tl !currentIfContext;
				x)
      | _ -> DoChildren
  end
end

let dsnsmtVisitor = new dsnsmtVisitorClass

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

  printf "****orig****\n";
  print_clauses clauses;

  printf "****reduced cheap****\n";
  let reduced3 = time reduce_trace_cheap  clauses in
  print_annotated_trace reduced3;

  printf "****unsat core****\n";
  let uc = time reduce_trace_unsatcore clauses in
  print_clauses uc;
  
  printf "****reduced both****\n";
  let reduced4 = time (cheap_then_expensive (propegate_interpolant_forward_linear 1)) clauses in
  print_clauses reduced4;




  exit_solver singleSolver

    

let feature : featureDescr = 
  { fd_name = "dsnsmt";
    fd_enabled = Cilutil.dsnSmt;
    fd_description = "Converts linearized concrete c program to SMT";
    fd_extraopt = [];
    fd_doit = dsnsmt;
    fd_post_check = true
  } 

