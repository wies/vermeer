(* TODOS
 * fix Int vs Bool problem - DONE
 * handle conditions from if statements - DONE?
 * handle operators that differ between c and smt eg && vs and
 * remap interpolants when returning them
 * fix the "ands" and extra () in the interpolation split
 *)
(** See copyright notice at the end of this file *)

(** Add printf before each function call *)

open Pretty
open Cil
open Trace
module E = Errormsg
module H = Hashtbl

(* issue if interpolant tries to go past where something is used *)

open String
open Printf
open Unix
open Map
open Set
(* consider using https://realworldocaml.org/v1/en/html/data-serialization-with-s-expressions.html *)

(******************************** Optimizations ***************************)
(* keep around the vars for a partition
 * there is a lot of stuff where I use @ instead of :: then reverse
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
type varSSAMap = smtvar VarSSAMap.t
type varTypeMap = smtVarType TypeMap.t
let emptySSAMap : varSSAMap = VarSSAMap.empty
let emptyTypeMap : varTypeMap = TypeMap.empty

type term = | SMTRelation of string * term list
	    | SMTConstant of int64
	    | SMTVar of smtvar 
	    | SMTTrue | SMTFalse

type problemType = SMTOnly | Interpolation of varSSAMap 

(* TODO record the program location in the programStmt *)
type clauseType = ProgramStmt | Interpolant

type sexpType = Sexp | SexpRel | SexpIntConst | SexpVar | SexpBoolConst

type clause = {formula : term; 
	       idx : int; 
	       vars : VarSet.t; 
	       ssaIdxs : varSSAMap;
	       typ : clauseType;
	       ifContext : term list
	      }

type smtResult = Sat | Unsat of clause option 


type program = {clauses : clause list;
		allVars : VarSet.t
	       }

type ifContext = term list

exception CantMap of smtvar


(******************** Globals *************************)
let count = ref 1
let print_bars msg str = print_string (msg ^ " |" ^ str ^"|\n")
let smtDir = "./smt/"
let outfile = smtDir ^ "outfile.smt2"
let infile = smtDir ^ "infile.smt2"
let name = ref ""
let currentFunc: string ref = ref ""
(*keep the program in reverse order, then flip once. Avoid unneccessary list creation*)
let revProgram : clause list ref = ref [] 
let typeMap : varTypeMap ref  = ref emptyTypeMap
let smtZero = SMTConstant(0L)
let emptyIfContext = []
let currentIfContext : ifContext ref = ref emptyIfContext
let flowSensitiveEncoding = true


(******************** Defs *************************)

let smtOpts = 
"(set-option :print-success false)
(set-option :produce-proofs true)
(set-logic QF_LIA)\n"

let smtCheckSat = "(check-sat)\n"
let smtExit = "(exit)\n"


(************************* utils *************************)
let rec last = function
    | [] -> None
    | [x] -> Some x
    | _ :: t -> last t;;

let rec all_but_last lst = match lst with
  | [] -> raise (Failure "empty list can't remove last")
  | [x] -> []
  | x::xs -> x :: (all_but_last xs)

let d_string (fmt : ('a,unit,doc,string) format4) : 'a = 
  let f (d: doc) : string = 
    Pretty.sprint 800 d
  in
  Pretty.gprintf f fmt 

let safe_mkdir name mask = 
  if Sys.file_exists name then ()
  else Unix.mkdir name mask

(****************************** Clauses ******************************)
(* two possibilities: either maintain a mapping at each point
 * or remap as we go starting from one end *)


(* So we need to figure out the type of each variable *)

let get_var_type (var : smtvar) : smtVarType = 
  if IntMap.mem var.vidx !typeMap then
    IntMap.find var.vidx !typeMap
  else 
    SMTUnknown

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
	  | "=" | "distinct" | "ite" -> 
	    (*we analyze the list twice.  Once to find out what kind it is
	     * the second time to propegate that result to everything in it *)
	    let t1 = analyze_type_list SMTUnknown l in
	    let t2 = second_if_matching t1 (analyze_type_list t1 l) in
	    second_if_matching typ t2	    
	  | "+" | "-" | "*" | "div" | "mod" | "abs" -> 
	    let _ = analyze_type_list SMTInt l in
	    second_if_matching typ SMTInt
	  | _ -> raise (Failure ("unexpected operator " ^ s))
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
	if VarSSAMap.mem vidx ssaMap
	then
	  let vOld = VarSSAMap.find vidx ssaMap in
	  if vOld.ssaIdx < v.ssaIdx then
	    VarSSAMap.add vidx v ssaMap
	  else
	    ssaMap
	else 
	  VarSSAMap.add vidx v ssaMap in
      make_ssa_map vs ssaMap

let make_clause (f: term) (i :int) (ssa: varSSAMap) (typ: clauseType) (ic : term list) 
    : clause = 
  let v  = get_vars [f] VarSet.empty in
  let ssa  = make_ssa_map (VarSet.elements v) ssa in
  let _ = analyze_var_type f in (* update the typemap to include this clause *)
  let c  = {formula = f; idx = i; vars = v; ssaIdxs = ssa; typ = typ; ifContext = ic} in
  c

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
  if VarSSAMap.mem oldVar.vidx ssaMap then
    Some (VarSSAMap.find oldVar.vidx ssaMap)
  else 
    None

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

(* I guess we should remap the if context too.  Does this make sense? *)
let remap_clause ssaMap cls = 
  make_clause 
    (remap_formula ssaMap cls.formula)
    cls.idx
    ssaMap
    cls.typ
    (List.map (remap_formula ssaMap) cls.ifContext)
    

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

let rec string_of_clause c = 
  string_of_formula c.formula

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
let rec debug_SSAMap_rec bindings = 
  match bindings with
    | [] -> ""
    | (k,v)::bs -> 
      "\t(" ^ string_of_int k
      ^ ", " ^ debug_var v
      ^ ")\n"
      ^ debug_SSAMap_rec bs

let debug_SSAMap m = 
  debug_SSAMap_rec (VarSSAMap.bindings m)

let rec debug_vars_rec vars = 
  match vars with
    | [] -> ""
    | v::vs -> "\t" ^ debug_var v ^ "\n" ^ debug_vars_rec vs
let debug_vars vars = 
  debug_vars_rec (VarSet.elements vars)

let rec debug_clause c = 
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

let assertion_name (c : clause) :string = "IP_" ^ (string_of_int c.idx)

let make_ifContext_formula ic = 
  match ic with 
    | [] -> SMTTrue
    | [x] -> x
    | _ -> SMTRelation("and",ic)

let make_assertion_string c =
  let form = 
    if flowSensitiveEncoding then
      SMTRelation("=>", 
		[make_ifContext_formula c.ifContext; 
		 c.formula])
    else c.formula in 
  "(assert (! " 
  ^ string_of_formula form
  ^ " :named " ^ assertion_name c
  ^ "))\n"
    
let make_interpolation_list program = 
  List.map (fun x -> (assertion_name x) ^ " " ) program

let rec get_all_vars_rec clauses  accum =
  match clauses with 
    | [] -> accum
    | x::xs -> 
      let accum =  VarSet.union x.vars accum in
      get_all_vars_rec xs accum

let get_all_vars clauses = 
  get_all_vars_rec clauses VarSet.empty

let make_var_decl vars =
  let f v = 
    let ts = string_of_vartype (get_var_type v) in
    "(declare-fun " ^ (string_of_var v)  ^" () " ^ ts ^ ")\n" 
  in
  List.map f (VarSet.elements vars)

(* DSN TODO replace this with analyzing the program once *)
let make_program clauses = 
  let vars = get_all_vars clauses in
  {clauses = clauses;
   allVars = vars;
  }

let make_smt_file prog cmds = 
  let decls = make_var_decl prog.allVars in
  let p_strings = List.map make_assertion_string prog.clauses in 
  [smtOpts] @ decls @ p_strings @ cmds @ [smtExit]

(******************** File creation ********************)



let make_interpolate_between before after = 
  let string_of_partition part = 
    match make_interpolation_list part with 
      | [] -> raise (Failure "should be a partition")
      | [x] -> x
      | xs -> 
	let names = List.fold_left (fun x y -> x ^ " " ^ y) "" xs in
	"(and " ^ names ^ ")"
  in
  let beforeNames = string_of_partition before in
  let afterNames = string_of_partition after in
  "(get-interpolants " ^ beforeNames ^ " " ^ afterNames ^ "))\n"

let print_to_file filename lines = 
  let oc = open_out filename in    (* create or truncate file, return channel *)
  let printf_oc = Printf.fprintf oc "%s" in
  let _  = List.map printf_oc lines in
  close_out oc                (* flush and close the channel *)
  

(******************** Input functions *************************)

(* for now only worry about ' ' *)
(* ocaml 4.0 would allow trim *)
let rec trim_rec_left str i = 
  if i = length str || str.[i] <> ' ' then
    i
  else 
    trim_rec_left str (i + 1)
    
let rec trim_rec_right str i = 
  if i < 0 || str.[i] <> ' ' then
    i
  else 
    trim_rec_right str (i - 1)

let trim_left str = trim_rec_left str 0
let trim_right str = trim_rec_right str ((length str) -1)

let trim str =
  if (contains str ' ' )then 
    let l_idx = trim_left str in
    let r_idx = trim_right str in
    let len = r_idx - l_idx + 1  in 
    let len = if (len < 0) then 0 else len in
    sub str l_idx len
  else 
    str

(* does this handle not correctly ?? *)
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
    | 'a' when str = "and" | 'd' when str = "distinct" 
    | 'o' when str = "or" | 'n' when str = "not"
    | 'x' when str = "xor" 
	  -> SexpRel
    | 'f' when str = "false" | 't' when str = "true" 
				   -> SexpBoolConst

    | _
      -> SexpVar
let split_on_underscore str = 
  if not ( contains str '_') then 
    raise (Failure "split on underscore missing underscore")
  else 
    let idx = rindex str '_' in
    let len = (length str) - idx - 1 in 
    (*-1 because we ignore the _ *)
    let lhs = sub str 0 idx in    
    let rhs  = sub str (idx + 1) len in
    (lhs,rhs)

(* canonical format: x_vidx_ssaidx *)
let smtVarFromString str = 
  let (lhs,ssa_str) = split_on_underscore str in
  let (lhs,vidx_str) = split_on_underscore lhs in
  {fullname = str; 
   vidx = (int_of_string vidx_str);
   ssaIdx =  (int_of_string ssa_str);
   owner = -1
  }
    
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


let rec extract_term (str) : term list = 
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
      | SexpConst -> 
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

let clause_from_form (f : term) (ssaBefore: varSSAMap) (ic : ifContext) : clause =
  let idx = !count in
  let _ = incr count in
  let cls : clause = make_clause f idx ssaBefore ProgramStmt ic in
  cls

let clause_from_sexp (sexp: string) (ssaBefore: varSSAMap) (ic : ifContext): clause = 
  let term_lst = extract_term sexp in
  let t = List.hd term_lst in (* should assert exactly one elt *)
  let idx = !count in
  let _ = incr count in
  let cls : clause = make_clause t idx ssaBefore ProgramStmt ic in
  cls

let begins_with str header = 
  let ls = length str in
  let lh = length header in
  if ls >= lh then
    let strHead = sub str 0 lh in
    strHead = header 
  else
    false

(* should I perhaps pass in the ssabefore *)
let rec parse_smtresult lines pt = 
  match lines with
    | []-> raise (Failure "bad smt result file")
    |  l::ls -> 
      if begins_with l "INFO" then 
	parse_smtresult ls pt (*skip *)
      else if begins_with l "unsat" then 
	match pt with
	  | SMTOnly -> Unsat(None)
	  | Interpolation(v) -> 
	    let cls = clause_from_sexp (List.hd ls) v emptyIfContext in
	    Unsat(Some(cls))
      else if begins_with l "sat" then
	Sat
      else 
	raise (Failure "unmatched line")

let input_lines filename = 
  let lines = ref [] in
  let chan = open_in filename in
  try
    while true; do
      lines := input_line chan :: !lines
    done; []
  with End_of_file ->
    close_in chan;
    List.rev !lines
      

let read_smtresult filename pt = 
  let lines = input_lines filename in
  parse_smtresult lines pt

(****************************** Interpolation ******************************)
let do_smt basename prog smtCmds pt =
  let solver_string = "java -jar /home/dsn/sw/smtinterpol/smtinterpol.jar" in
  let smtDir = "./smt" in
  let _ = safe_mkdir smtDir 0o777 in
  let basename = smtDir ^ "/" ^ basename in
  let inFilename = basename ^ ".smt2"  in
  let resultFilename = basename ^ "_out.smt2"  in
  let logFilename = "log.txt" in
  let args = 
    " " ^ inFilename  
    ^ " > " ^ resultFilename
    ^ " 2> " ^ logFilename in
  let smtFile = make_smt_file prog smtCmds in
  let _ = print_to_file inFilename smtFile in
  let _ = Sys.command (solver_string ^ args) in
  read_smtresult resultFilename pt

let is_valid_interpolant (before :clause list) (after : clause list) (inter :clause) = 
  let ssa = match (last before) with
    | Some(x) -> x.ssaIdxs
    | None -> raise (Failure "is_valid_interpolant before should have elements") in
  let probType = SMTOnly in
  let inter = remap_clause ssa inter in
  let not_inter = negate_clause inter in
  let before_p = make_program (not_inter :: before) in
  let before_cmds = [smtCheckSat] in
  match do_smt "before" before_p before_cmds probType with
    | Sat -> false
    | Unsat(_) -> 
      let after_p = make_program (inter :: after) in
      let after_cmds = [smtCheckSat] in
      match do_smt "after" after_p after_cmds probType with
	| Sat -> false
	| Unsat(_) -> true 

(* keep the leftSuffix in reversed order
 * the last two elements of the leftSuffix are the currentState
 * and the first update after that 
 *)
let rec find_farthest_point_interpolant_valid 
    (currentState :clause) (interpolant :clause) 
    (leftSuffix : clause list) (rightSuffix :clause list) =
  match leftSuffix with
    | [] -> raise (Failure "should be at least one thing here")
    | [_] ->  rightSuffix
    | _ -> 
      let x = match last leftSuffix with 
	| Some(c) -> c
	| None -> raise (Failure "should have more here!") in
      let leftSuffix = all_but_last leftSuffix in
      let rightSuffix = x :: rightSuffix in
      let before = currentState :: leftSuffix in
      let after  = rightSuffix in
      if (is_valid_interpolant before after interpolant) then
	rightSuffix
      else
	find_farthest_point_interpolant_valid 
	  currentState interpolant leftSuffix rightSuffix


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
 *)
let rec reduce_trace_imp reducedPrefix currentState unreducedSuffix =
  match unreducedSuffix with
    | [] -> reducedPrefix
    | [x] -> reducedPrefix @ [x]
    | x :: xs ->
      let clist = currentState :: unreducedSuffix in
      let p = make_program clist in
      let before = [currentState;x] in
      let after = xs in
      let smt_cmds = [smtCheckSat ; make_interpolate_between before after] in
      let probType = Interpolation x.ssaIdxs in
      match do_smt "foo" p smt_cmds probType with 
	| Unsat (Some(interpolant)) -> 
	  let unreducedSuffix = find_farthest_point_interpolant_valid 
	    currentState interpolant unreducedSuffix [] in
	  reduce_trace_imp 
	    (reducedPrefix @ [currentState; x])
	    interpolant
	    unreducedSuffix
	| Unsat (None) -> raise (Failure "couldn't find interpolant")
	| Sat -> raise (Failure "was sat")

(*********************************C to smt converstion *************************************)
let rec formula_from_lval l = 
  match l with 
    | (Var(v),_) -> SMTVar(smtVarFromString(v.vname))
    | _ -> raise (Failure "should only have lvals of type var")

(*DSN TODO check if there are any differences in cilly vs smt opstrings *)
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
    let opArg = d_string "%a" d_binop o in
    let eForm1 = formula_from_exp e1 in
    let eForm2 = formula_from_exp e2 in
    SMTRelation(opArg,[eForm1;eForm2])
  | _ -> raise (Failure "not handelling this yet") 

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
	let cls = clause_from_form assgt ssaBefore !currentIfContext in
	revProgram := cls :: !revProgram;
	DoChildren
    | Call(lo,e,al,l) ->
      let fname = d_string "%a" d_exp e in
      if fname = "assert" then
	(*assert should have exactly one element asserted *)
	let form = formula_from_exp (List.hd al) in
	let form = make_bool form in 
	let ssaBefore = get_ssa_before() in
	let cls = clause_from_form form ssaBefore !currentIfContext in
	revProgram := cls :: !revProgram;
	DoChildren
      else
	raise (Failure "shouldn't have calls in a concrete trace")
    | _ -> DoChildren
  end
  method vstmt (s : stmt) = begin
    match s.skind with
      | If(i,t,e,l) ->
	if not (e.bstmts = []) then raise (Failure "else block not handeled") 
	else
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
  let reduced = reduce_trace_imp [] (List.hd clauses) (List.tl clauses) in
  let _ = List.map (fun x-> printf "%s\n" (string_of_clause x)) reduced in
  ()
  

let feature : featureDescr = 
  { fd_name = "dsnsmt";
    fd_enabled = Cilutil.dsnSmt;
    fd_description = "Converts linearized concrete c program to SMT";
    fd_extraopt = [];
    fd_doit = dsnsmt;
    fd_post_check = true
  } 

