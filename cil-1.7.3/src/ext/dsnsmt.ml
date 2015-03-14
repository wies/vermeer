(* TODOS
 * fix Int vs Bool problem - DONE
 * handle conditions from if statements - DONE?
 * handle operators that differ between c and smt eg && vs and
 * remap interpolants when returning them
 * fix the way that I cast if context
 * SMTVar should have subtypes
 *)

open Cil
open Dsnutils
open Dsnsmtdefs

(* issue if interpolant tries to go past where something is used *)

(* consider using https://realworldocaml.org/v1/en/html/data-serialization-with-s-expressions.html *)

let smtCallTime = ref []

module HazardSet = Dsngraph.HazardSet

(* DSN TODO just pass this around *)
type smtContext = 
  {
    typeMap: varTypeMap;
    seenThreads : TIDSet.t;
    seenGroups : GroupSet.t;
    clauses : clause list;
    graph : Dsngraph.G.t option;
  }

(* a bit of a hack - yet another global :( *)
(* typemap should go in here too *)
let smtContext = ref {
  typeMap = emptyTypeMap;
  seenThreads = TIDSet.empty;
  seenGroups = GroupSet.empty;
  clauses = [];
  graph = None
}

(******************************** Optimizations ***************************)
(* keep around the vars for a partition
*)

(*******************************TYPES *************************************)
type sexpType = | Sexp 
		| SexpRel 
		| SexpLet
		| SexpIntConst 
		| SexpBoolConst
		| SexpSsaVar of smtSsaVar 
		| SexpLetVar 
		| SexpFlagVar 

(******************** Defs *************************)
let smtDir = "./smt/"
let smtCheckSat = "(check-sat)\n"
let smtGetUnsatCore = "(get-unsat-core)\n"

let smtZero = SMTConstant(0L)
let smtOne = SMTConstant(1L)
let emptyIfContext = []

(******************** Globals *************************)

let typeMap : varTypeMap ref  = ref emptyTypeMap
let count = ref 1


let get_var_type (var : smtSsaVar) : smtVarType = 
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
  | SMTSsaVar(v) -> string_of_var v
  | SMTLetVar(v) -> v
  | SMTFlagVar v -> v
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
  | SMTSsaVar(v) -> debug_var v
  | SMTLetVar(v) -> v
  | SMTFlagVar v -> v
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


(****************************** Encoding in smt strings ******************************)
(* Given a clause, and a term, encode that term into a new term
 * suitable for SMT processing
 * possibily adding new flags, dependencies, etc 
 * Since we are using functions, can hide lots of interresting stuff in the 
 * curried variables *)
type encodingFn = clause -> term -> term
type encodingFunctions = 
  {mutable makeFlowSensitive : encodingFn;
   mutable makeFlag : encodingFn;
   mutable makeHazards : encodingFn;
  }
let identityEncodingFn clause formula = formula

let identityEncoding () = {
  makeFlowSensitive = identityEncodingFn;
  makeFlag =  identityEncodingFn;
  makeHazards = identityEncodingFn;
}

(*this is mutable, so we can change the default encoding *)
let currentEncoding = identityEncoding()

(* useful encoding functions *)
let make_dependent_on (dependencyList: term list) (formula : term) = 
  match dependencyList with
  | [] -> formula
  | [x] -> SMTRelation ("=>", [x;formula])
  | _ -> let dependency = SMTRelation("and", dependencyList) in
	 SMTRelation("=>", [dependency; formula]) 

let make_flowsensitive clause formula = 
  make_dependent_on (List.map (fun x -> x.iformula) clause.ifContext) formula

let encode_flowsensitive () = 
  currentEncoding.makeFlowSensitive <- make_flowsensitive

let make_flowsensitive_this_tid tid clause formula = 
  match clause.typ with
  | ProgramStmt(_,None) -> failwith "expected a tid here"
  | ProgramStmt(instr, Some thatTid) when thatTid <> tid ->
    identityEncodingFn clause formula
  | _ ->
    make_flowsensitive clause formula

let encode_flowsensitive_this_tid tid = 
  currentEncoding.makeFlowSensitive <- make_flowsensitive_this_tid tid

let flag_var_string c = "flag_" ^ clause_name c
let get_flag_var c = SMTFlagVar (flag_var_string c)

let make_flag clause formula = 
  match clause.typ with 
  | ProgramStmt _ ->   
    SMTRelation("and", [formula;get_flag_var clause])
  | _ -> formula

let encode_flag () = 
  currentEncoding.makeFlag <- make_flag

(* make sure that make_flags is set if we use this!*)
let make_hazards graph hazards intrathreadHazards clause formula = 
  if HazardSet.is_empty hazards then 
    formula 
  else match clause.typ with 
  | ProgramStmt _ ->   
    let hazard_preds = Dsngraph.get_hazard_preds graph hazards clause in
    let hazard_preds = 
      if intrathreadHazards then hazard_preds 
      else 
	let clstid = extract_tid clause in
	Dsngraph.ClauseSet.filter 
	  (fun x -> (extract_tid x) <> clstid) hazard_preds in
    let pred_flags = 
      Dsngraph.ClauseSet.fold (fun e a -> (get_flag_var e)::a) hazard_preds [] in
    make_dependent_on pred_flags formula
  | _ -> formula

let encode_hazards graph hazards intrathreadHazards = 
  encode_flag ();
  currentEncoding.makeHazards <- make_hazards graph hazards intrathreadHazards

(* Important that we make the flag first, cause it has to go inside the dependency *)
let encode_formula opts clause = 
  let form = clause.formula in
  let form = opts.makeFlag clause form in
  let form = opts.makeFlowSensitive clause form in
  let form = opts.makeHazards clause form in
  "(assert (! " 
  ^ string_of_formula form
  ^ " :named " ^ clause_name clause
  ^ "))\n"
    
    
let make_var_decl v =
  let ts = string_of_vartype (get_var_type v) in
  "(declare-fun " ^ (string_of_var v)  ^" () " ^ ts ^ ")\n" 
let make_flag_decl c = 
  "(declare-fun " ^ (flag_var_string c)  ^" () Bool )\n" 

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

(****************************** Formula processing ******************************)

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
  let update_type (var : smtSsaVar) newType = 
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
    | SMTFlagVar _ -> failwith "shouldn't be parsing this!"
    | SMTFalse | SMTTrue -> SMTBool
    | SMTConstant(_) -> SMTInt
    | SMTSsaVar(v) -> get_var_type v
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
	failwith "not supporting bit operators"
      | _ -> failwith ("unexpected operator in analyze type |" ^ s ^ "|")
    end
  and analyze_type_lst l = List.fold_left 
    (fun a x -> second_if_matching a (analyze_type x)) SMTUnknown l
  in
  let rec assign_vartypes desired f =
    match f with
    | SMTLetBinding _ -> failwith "shouldn't be parsing this!"
    | SMTLet _ -> failwith "shouldn't be parsing this!"
    | SMTFlagVar _ -> failwith "shouldn't be parsing this!"
    | SMTLetVar _ -> failwith "shouldn't be parsing this!"
    | SMTFalse | SMTTrue | SMTConstant _ -> ()
    | SMTSsaVar(v) -> update_type v desired
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
	failwith "not supporting bit operators"
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
    | SMTFlagVar _ -> failwith "shouldn't be parsing this!"
    | SMTFalse | SMTTrue | SMTConstant _ | SMTSsaVar _ -> make_cast desired f
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
	failwith "not supporting bit operators"
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
    | SMTConstant _ | SMTFalse | SMTTrue | SMTLetVar _ | SMTFlagVar _ -> set
    | SMTSsaVar(v) -> VarSet.add v set 
    | SMTLetBinding(v,e) -> get_vars [e] set


(****************************** Clauses ******************************)
(* two possibilities: either maintain a mapping at each point
 * or remap as we go starting from one end *)


(* So we need to figure out the type of each variable *)



(* this function does two things: It determines the type of the 
 * expression.  It also updates the mapping with any newly discovered
 * var -> type mappings
 *)


let count_basevars clauses = 
  BaseVarSet.cardinal (all_basevars clauses)

let count_basevars_at a = count_basevars (trace_from_at a)



let get_vars_ic icList set = 
  List.fold_left (fun a e -> get_vars [e.iformula] a) set icList


(* the first time we see a new index, we know we have a defn for it *)
let make_clause (f: term) (ssa: varSSAMap) (ic : ifContextList) 
    (ct: clauseType) (tags : clauseTag list)
    : clause = 
  let rec make_ssa_map (vars : smtSsaVar list) (ssaMap : varSSAMap) (defs : VarSet.t) 
      : (varSSAMap * VarSet.t) =
    let alreadyDefined v = 	
      try let vOld = VarSSAMap.find v.vidx ssaMap in
	  vOld.ssaIdx >= v.ssaIdx 
      with Not_found -> false in
    match vars with 
    | [] -> ssaMap, defs
    | v :: vs -> 
      let vidx = v.vidx in
      let ssaMap,defs = 
	if (alreadyDefined v) then (ssaMap,defs)
	else (VarSSAMap.add vidx v ssaMap, VarSet.add v defs)
      in
      make_ssa_map vs ssaMap defs in
  incr count;
  let v  = get_vars [f] emptyVarSet in
  let v = get_vars_ic ic v in
  let ssa,defs  = make_ssa_map (VarSet.elements v) ssa VarSet.empty in
  let f = match ct with
    | ProgramStmt _ ->  type_check_and_cast_to_bool f
    | _ -> f
  in
  let c  = {formula = f; 
	    idx = !count; 
	    vars = v; 
	    defs = defs;
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
    | SMTConstant(_) | SMTFalse | SMTTrue | SMTLetVar _ | SMTFlagVar _ as form -> form
    | SMTSsaVar(v) ->
      let newVarOpt = get_current_var v ssaMap in
      match newVarOpt with
      | Some (newVar) -> SMTSsaVar(newVar)
      | None -> 
	print_endline ("can't map " ^ string_of_var v 
		       ^ "\nin formula " ^ string_of_formula form);
	print_ssa_map ssaMap;
	raise (CantMap v)
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
  let str = List.fold_left (fun accum elem -> accum ^ " " ^ (clause_name elem)) "" program in
  "(get-interpolants " ^ str ^ ")\n"

let make_interpolate_between before after = 
  let string_of_partition part = 
    match part with 
    | [] -> failwith "should be a partition"
    | [x] -> clause_name x
    | _ -> 
      let names = List.fold_left 
	(fun accum elem -> (clause_name elem) ^ " " ^ accum) "" part in
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
let getFirstArgType str = 
  let is_cse_var s = Str.string_match (Str.regexp ".cse[0-9]+") s 0 in
  let is_flag_var s = begins_with  s "flag_" 
  in
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
      ->  failwith "not supporting bit operators"
    | "false" | "true" 
      -> SexpBoolConst
    | _ when (is_cse_var str) -> SexpLetVar
    | _ when (is_flag_var str) -> SexpFlagVar
    (* if its not a known type, just assume its ssa var.  The conversion function
     * will throw is this doesn't work *)
    | _ -> SexpSsaVar (smtSsaVarFromString str) 
    end

let extract_unsat_core (str) : string list = 
  let str = strip_parens str in
  Str.split (Str.regexp "[ \t]+") str

let rec extract_term (str)  : term list = 
  (* returns the first sexp as a string,
   * and the remainder as another string *)
  let extract_first_sexp str = 
    let str = trim str in
    let len = String.length str in
    if len = 0 then failwith "nothing here"
    else if (str.[0] = '(') then
      let endIdx = matchParensRec str 1 1 in 
      let lhs = String.sub str 0 (endIdx +1) in 
      (* +1 avoid the closing paren *)
      let rhs = String.sub str (endIdx + 1) (len - endIdx - 1) in
      (trim lhs, trim rhs)
    else 
      let endIdx = findEndOfWord str in
      if endIdx = len then 
	(str,"")
      else 
	let lhs = String.sub str 0 (endIdx) in 
	let rhs = String.sub str (endIdx + 1) (String.length str - endIdx - 1) in
	(trim lhs, trim rhs)
  in
  let str = strip_parens (trim str) in
  if String.length str = 0 then 
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
    | SexpSsaVar v ->
      let tailExp = extract_term tailStr in
      let term = SMTSsaVar(v) in
      term :: tailExp
    | SexpLetVar ->
      let tailExp = extract_term tailStr in
      let term = SMTLetVar(headStr) in
      term :: tailExp
    | SexpFlagVar ->
      let tailExp = extract_term tailStr in
      let term = SMTFlagVar(headStr) in
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





(****************************** Solver definitions ******************************)
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
let declare_unknown_sort solver = write_line_to_solver solver "(define-sort Unknown () Int)\n"
  
let reset_solver solver = write_line_to_solver solver "(reset)\n"

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

(* keep a map of active solvers *)
module SolverMap = Map.Make(String)
type solverMap = solver_state SolverMap.t
let emptySolverMap : solverMap = SolverMap.empty
let activeSolvers = ref emptySolverMap

(* get the solver.  Create if necessary *)
let _create_or_get_solver session_name solver do_log = 
  try SolverMap.find session_name !activeSolvers
  with Not_found -> 
    (* Given a description of a solver, start the solver and create pipes to it *)
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
    activeSolvers := SolverMap.add session_name state !activeSolvers;
    state 
      
let getSmtinterpol () = 
  _create_or_get_solver "smtinterpol_out" {name = "smtinterpol"; info=smtinterpol_2_1} true 

let getZ3 () = 
  _create_or_get_solver "z3_out" {name = "z3"; info=z3_4_3} true

let _exit_solver solver = write_line_to_solver solver "(exit)\n"; flush_solver solver
let exit_solver session_name = 
  try let solver = SolverMap.find session_name !activeSolvers in
      _exit_solver solver;
      activeSolvers := SolverMap.remove session_name !activeSolvers
  with Not_found -> ()

let exit_all_solvers () = 
  SolverMap.iter (fun k v -> _exit_solver v) !activeSolvers;
  activeSolvers := emptySolverMap

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
  (* on occation, there are variables that are never used in a way where their type matters
   * assume they're ints *)
  declare_unknown_sort solver;
  (*write the declerations *)
  let allVars = all_vars clauses in
  VarSet.iter (fun v -> write_line_to_solver solver (make_var_decl v)) allVars;
  (* declare the flags vars *)
  (*this is a bit of a hack.  We should really only do this for the ones we need *)
  List.iter (fun c -> write_line_to_solver solver (make_flag_decl c)) !smtContext.clauses;
  (* write the program clauses *)
  List.iter (fun x -> write_line_to_solver solver (encode_formula currentEncoding x)) clauses;
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
    | SMTConstant(_) | SMTFalse | SMTTrue | SMTLetVar _ | SMTFlagVar _ -> form
    | SMTSsaVar(v) -> SMTSsaVar {v with ssaIdx=0}
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


(****************************** Statistics ******************************)

let print_trace_linenums x = List.iter (fun c -> Printf.printf "%s\n" (print_linenum c)) x;
  flush stdout
let print_annotatedtrace_linenums x = List.iter (fun (_,c) -> Printf.printf "%s\n" (print_linenum c)) x;
  flush stdout

(* could make tailrec by using revmap *)
let reduced_linenums x = 
  let nums = List.map print_linenum x in
  let nums = List.filter (fun x -> x <> "") nums in
  compress nums
let reduced_linenums_at x = reduced_linenums (trace_from_at x)

let print_reduced_linenums x = 
  let reduced = reduced_linenums x in
  List.iter (Printf.printf "%s\n") reduced

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

let calculate_stats (description : string) (trace : clause list)  = 
  let switches = count_contextswitches trace in
  let stmts = count_statements trace in
  let numvars = count_basevars trace in
  Printf.printf "%s\tSwitches: %d\tStmts: %d\tVars: %d\n"
    description switches stmts numvars
    
let calculate_thread_stats seenThreads (trace : clause list) = 
  TIDSet.iter (fun tid -> 
    let tidStmts = List.filter 
      (fun c -> match c.typ with | ProgramStmt _ -> (extract_tid c) = tid | _ -> false) 
      trace in
    calculate_stats ("Init" ^ string_of_int tid) tidStmts ) seenThreads
    
let calculate_stats_at  description at = 
  calculate_stats description (trace_from_at at)

