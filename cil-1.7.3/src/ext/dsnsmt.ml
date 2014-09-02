(* TODOS
 * remove the scope stuff
 * fix how indents work
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
module VarSSAMap = Map.Make(Int) 
module VarNameMap = Map.Make(String)
type varSSAMap = smtvar VarSSAMap.t
let emptySSAMap : varSSAMap = VarSSAMap.empty


type term = | SMTRelation of string * term list
	    | SMTConstant of int64
	    | SMTVar of smtvar 

type problemType = SMTOnly | Interpolation of smtvar VarSSAMap.t 

(* TODO record the program location in the programStmt *)
type clauseType = ProgramStmt | Interpolant

type sexpType = Sexp | SexpRel | SexpConst | SexpVar

type clause = {formula : term; 
	       idx : int; 
	       vars : VarSet.t; 
	       ssaIdxs : varSSAMap;
	       typ : clauseType
	      }

type smtResult = Sat | Unsat of clause option 


type program = {clauses : clause list;
		allVars : VarSet.t
	       }

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

let rec all_but_last accum lst = match lst with
  | [] -> raise (Failure "empty list can't remove last")
  | [x] -> []
  | x::xs -> s :: (all_but_last xs)

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

(* not tail recursive *)
let rec get_vars formulaList set = 
  match formulaList with 
    | [] -> set
    | x::xs ->
      let set = get_vars xs set in
      match x with
	| SMTRelation(s,l) -> get_vars l set
	| SMTConstant(_) -> set
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

let make_clause (f: term) (i :int) (ssa:  varSSAMap) (typ: clauseType): clause= 
  let v  = get_vars [f] VarSet.empty in
  let ssa  = make_ssa_map (VarSet.elements v) ssa in
  let c  = {formula = f; idx = i; vars = v; ssaIdxs = ssa; typ = typ} in
  c

let negate_clause cls = 
  {formula = SMTRelation("not",[cls.formula]);
   idx = cls.idx;
   vars = cls.vars;
   ssaIdxs = cls.ssaIdxs;
   typ = cls.typ}

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
    | SMTConstant(_) -> form
    | SMTVar(v) ->
      let newVarOpt = get_current_var v ssaMap in
      match newVarOpt with
	| Some (newVar) -> SMTVar(newVar)
	| None -> raise (CantMap v)

let remap_clause ssaMap cls = 
  make_clause 
    (remap_formula ssaMap cls.formula)
    cls.idx
    ssaMap
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

let assertion_name (c : clause) :string = "IP_" ^ (string_of_int c.idx)

let make_assertion_string c =
  "(assert (! " 
  ^ string_of_clause c
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
  let f v = "(declare-fun " ^ (string_of_var v)  ^" () Int)\n" in
  List.map f (VarSet.elements vars)

let make_program clauses = 
  let vars = get_all_vars clauses in
  {clauses = clauses;
   allVars = vars}

let make_smt_file prog cmds = 
  let decls = make_var_decl prog.allVars in
  let p_strings = List.map make_assertion_string prog.clauses in 
  [smtOpts] @ decls @ p_strings @ cmds @ [smtExit]

(******************** File creation ********************)

let make_interpolate_between before after = 
  let before_list  = make_interpolation_list before in
  let after_list = make_interpolation_list after in
  let before_names = List.fold_left (fun x y -> x ^ " " ^ y) "" before_list in
  let after_names = List.fold_left (fun x y -> x ^ " " ^ y) "" after_list in
  "(get-interpolants (and " ^ before_names ^ ") (and " ^ after_names ^ "))\n"


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


let getFirstArgType str = 
  let str = trim str in
  match str.[0] with
    | '(' -> Sexp
    | '0' -> SexpConst
    | '1' -> SexpConst
    | '2' -> SexpConst
    | '3' -> SexpConst
    | '4' -> SexpConst
    | '5' -> SexpConst
    | '6' -> SexpConst
    | '7' -> SexpConst
    | '8' -> SexpConst
    | '9' -> SexpConst
    | '=' -> SexpRel
    | '<' -> SexpRel
    | '>' -> SexpRel
    | '-' -> SexpRel
    | '+' -> SexpRel
    | '*' -> SexpRel
    | _   -> SexpVar

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

let clause_from_form (f : term) (ssaBefore: varSSAMap) : clause =
  let idx = !count in
  let _ = incr count in
  let cls : clause = make_clause f idx ssaBefore ProgramStmt in
  cls

let clause_from_sexp (sexp: string) (ssaBefore: varSSAMap) : clause = 
  let term_lst = extract_term sexp in
  let t = List.hd term_lst in (* should assert exactly one elt *)
  let idx = !count in
  let _ = incr count in
  let cls : clause = make_clause t idx ssaBefore ProgramStmt in
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
	    let cls = clause_from_sexp (List.hd ls) v in
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
  let args = 
    " " ^ inFilename  
    ^ " > " ^ resultFilename in
  let smtFile = make_smt_file prog smtCmds in
  let _ = print_to_file inFilename smtFile in
  let _ = Sys.command (solver_string ^ args) in
  read_smtresult resultFilename pt

let is_valid_interpolant before after inter = 
  let ssa = match last before with
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
    currentState 
    interpolant 
    leftSuffix 
    rightSuffix =
  match leftSuffix with
    | [] -> rightSuffix
    | _ -> 
      let x = last leftSuffix in
      let leftSuffix = all_but_last leftSuffix in
      let rightSuffix = x :: rightSuffix in
      let before = currentState @ leftSuffix in
      let after  = rightSuffix in
      if (is_valid_interpolant before after interpolant) then
	rightSuffix
      else
	find_farthest_point_interpolant_valid interpolant 
	  currentState 
	  interpolant
	  leftSuffix
	  rightSuffix


(* reduced is the prefix of the trace *)
(* We will work as follows:
 * For efficiency, store reducedPrefix in reversed order
 *
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
  match unreduced with
    | [] -> List.rev (current :: reduced)
    | [x] -> List.rev (x :: current :: reduced)
    | x :: xs ->
      let nextStep = 

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
  | _ -> raise (Failure "") 

(*
| 	SizeOf of typ 	(*	sizeof(<type>). Has unsigned int type (ISO 6.5.3.4). This is not turned into a constant because some transformations might want to change types	*)
| 	SizeOfE of exp 	(*	sizeof(<expression>)	*)
| 	SizeOfStr of string 	(*	sizeof(string_literal). We separate this case out because this is the only instance in which a string literal should not be treated as having type pointer to character.	*)
| 	AlignOf of typ 	(*	This corresponds to the GCC __alignof_. Has unsigned int type	*)
| 	AlignOfE of exp
| 	UnOp of unop * exp * typ 	(*	Unary operation. Includes the type of the result.	*)
| 	BinOp of binop * exp * exp * typ 	(*	Binary operation. Includes the type of the result. The arithmetic conversions are made explicit for the arguments.	*)
| 	CastE of typ * exp 	(*	Use Cil.mkCast to make casts.	*)
| 	AddrOf of lval 	(*	Always use Cil.mkAddrOf to construct one of these. Apply to an lvalue of type T yields an expression of type TPtr(T). Use Cil.mkAddrOrStartOf to make one of these if you are not sure which one to use.	*)
| 	StartOf of lval
*)

(* Return the sexp and the rest *)
(* TODO this can be done more efficiently*)
let main () = 
  let str1 = "(= x_1_1 x_2_1)" in            (*x = y *)
  let str2 = "(= x_1_2 (+ x_1_1 1))" in      (*x++   *)
  let str3 = "(= (+ x_1_2 1) x_1_3  )" in      (*x++   *)
  let str4 = "(> x_2_1 x_1_3)" in            (*y > x *)
  let c1 = clause_from_sexp str1 emptySSAMap in
  let c2 = clause_from_sexp str2 (c1.ssaIdxs) in 
  let c3 = clause_from_sexp str3 (c2.ssaIdxs) in 
  let c4 = clause_from_sexp str4 (c3.ssaIdxs) in 
  let clist = [c1;c2;c3;c4] in
  let p = make_program clist in
  let smt_cmds = [smtCheckSat ; make_interpolate_between [c1;c2] [c3;c4]] in
  let smt_file = make_smt_file p smt_cmds in
  (* Write message to file *)
  let probType = Interpolation c2.ssaIdxs in
  let x = do_smt "foo" p smt_cmds probType in 
  let _ =  match x with  
    | Unsat (Some(c)) -> 
      printf "unsat: %s\n" (string_of_clause c);
      printf "%B\n" (is_valid_interpolant [c1;c2;c3] [c4] c)
    | Unsat (None) -> printf "Unsat none\n"
    | Sat -> printf "sat\n" in
  () 
;;



class dsnsmtVisitorClass = object
  inherit nopCilVisitor

  method vinst i = begin
    match i with
      |  Set(lv, e, l) -> 
	let lvForm = formula_from_lval lv in
	let eForm = formula_from_exp e in
	let assgt = SMTRelation("=",[lvForm;eForm]) in
	let ssaBefore = match !revProgram with
	  | [] -> emptySSAMap
	  | x::xs -> x.ssaIdxs in
	let cls = clause_from_form assgt ssaBefore in
	revProgram := cls :: !revProgram;
	DoChildren
    | Call(lo,e,al,l) ->
      raise (Failure "shouldn't have calls in a concrete trace")
    | _ -> DoChildren
  end
  method vstmt (s : stmt) = begin
    match s.skind with
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
  let p = make_program (List.rev !revProgram) in
  let x = do_smt "foo" p [smtCheckSat] SMTOnly in 
  let _ =  match x with  
    | Unsat (Some(c)) -> 
      printf "unsat: some\n" ;
    | Unsat (None) -> printf "Unsat none\n"
    | Sat -> printf "sat\n" in
  () 

let feature : featureDescr = 
  { fd_name = "dsnsmt";
    fd_enabled = Cilutil.dsnSmt;
    fd_description = "Converts linearized concrete c program to SMT";
    fd_extraopt = [];
    fd_doit = dsnsmt;
    fd_post_check = true
  } 

(*
 *
 * Copyright (c) 2001-2002, 
 *  George C. Necula    <necula@cs.berkeley.edu>
 *  Scott McPeak        <smcpeak@cs.berkeley.edu>
 *  Wes Weimer          <weimer@cs.berkeley.edu>
 * All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 * 1. Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 *
 * 3. The names of the contributors may not be used to endorse or promote
 * products derived from this software without specific prior written
 * permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
 * IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
 * PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER
 * OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 *)
