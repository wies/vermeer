(*******************************TYPES *************************************)
open Dsnutils
module SMT = SmtSimpleAst

type varOwner = | Thread of int 
		| Global
    
type ssaVar = 
  {fullname : string; 
   vidx: int; 
   owner : int; 
   ssaIdx : int;
  }

(* canonical format: x_vidx_ssaidx *)
let ssaVarFromString str = 
  match split_on_underscore str with
  | [prefix;vidxStr;ssaIdxStr] -> 
    if prefix <> "x" then failwith ("invalid prefix " ^ prefix);
    {fullname = str; 
     vidx = (int_of_string vidxStr);
     ssaIdx =  (int_of_string ssaIdxStr);
     owner = -1
    }
  | _ -> failwith ("variable " ^ str ^ "is not in the valid format")

let ssaVarOptFromString str = 
  try Some (ssaVarFromString str) with
  | _ -> None

let is_ssa_var str = 
  match ssaVarOptFromString str with
  | Some _ -> true
  | None -> false

let is_flag_var s = begins_with  s "flag_" 
let is_hb_var s = begins_with s "hb_"
let is_cse_var s = Str.string_match (Str.regexp ".cse[0-9]+") s 0 

let remap_ssa_var_str str newIdx =
  match split_on_underscore str with
  | [prefix;vidxStr;ssaIdxStr] -> 
    if prefix <> "x" then failwith ("invalid prefix " ^ prefix);
    prefix ^ "_" ^ vidxStr ^ "_" ^ string_of_int newIdx
  | _ -> failwith ("variable " ^ str ^ "is not in the valid format")


module SSAVar = struct 
  type t = ssaVar
  let compare = Pervasives.compare end ;;
(* Given a variable name determine the correct mapping for it *)
module SSAVarMap = Map.Make(SSAVar)
module SSAVarSet = Set.Make(SSAVar)
module IntMap = Map.Make(Int)
module VarSSAMap = Map.Make(Int)
module TypeMap = Map.Make(Int)
module StringMap = Map.Make(String)
module StringSet = Set.Make(String)
module TIDSet = Set.Make(Int)
module GroupSet = Set.Make(Int)
module BaseVarSet = Set.Make(Int)
type varSSAMap = ssaVar VarSSAMap.t
let emptySSAMap : varSSAMap = VarSSAMap.empty
let emptyStringSet = StringSet.empty

let smtVarDefLoc : Cil.location SSAVarMap.t ref = ref SSAVarMap.empty
let get_location_line v = 
  let open Cil in
  let l = SSAVarMap.find v !smtVarDefLoc 
  in l.line


(* A let can take a list of bindings that it applies
 * So we SMTLet which takes a list of SMTLetBindings, which are of the 
 * form (SMTLetVar, term)
 * Eventually, this should all be cleaned up by encoding the whole thing in
 * some proper grammer.
 *)
type term = SmtSimpleAst.term

(* TODO record the program location in the programStmt *)
type clauseType = ProgramStmt of Cil.instr * int option 
		  | Interpolant | Constant | EqTest  
		  | Summary of  (Cil.instr * int option ) list
		  | Axiom of string


type ifContextElem = {iformula : term; istmt : Cil.stmt}
type ifContextList = ifContextElem list

type clauseTag = ThreadTag of int | LabelTag of string | SummaryGroupTag of int
let noTags = []

let string_of_tag  = function 
  | ThreadTag i -> "Thread_" ^ string_of_int i
  | LabelTag s -> "Label_" ^ s
  | SummaryGroupTag g -> "Group_" ^ string_of_int g

let string_of_tags tags = List.fold_left (fun a x -> "//" ^ string_of_tag x ^ "\n" ^ a) "" tags

let rec label_string = function
  | LabelTag _ as l :: _ -> string_of_tag l
  | x::xs -> label_string xs
  | [] -> ""

type clause = {formula : term; 
	       idx : int; 
	       ssaVars : SSAVarSet.t;
	       defs : SSAVarSet.t;
	       ssaIdxs : varSSAMap;
	       typ : clauseType;
	       ifContext : ifContextList;
	       cTags : clauseTag list
	      }

let emptyClause = {
  formula = SmtSimpleAstBuilder.mk_true;
  idx = -1;
  ssaVars = SSAVarSet.empty;
  defs = SSAVarSet.empty;
  ssaIdxs = VarSSAMap.empty;
  typ = Constant;
  ifContext = [];
  cTags = [];
}


type trace = clause list

(* An annotated trace pairs a clause representing an instruction
 * with the term which represents its precondition *)
type annotatedTrace = (term * clause) list
type problemType = CheckSat | GetInterpolation | GetUnsatCore
type smtResult = 
| Sat 
| Unsat  
| Unknown 
| Interpolant of term list 
| UnsatCore of StringSet.t 
type forwardProp = InterpolantWorks of clause * clause list | NotKLeft | InterpolantFails

exception CantMap of ssaVar

let clause_name (c : clause) :string = 
  match c.typ with
  | ProgramStmt(_) -> 
    (* as long as labels are unique, this will work just fine *)
    let prefix = label_string c.cTags in
    if prefix <> "" then prefix 
    else "PS_" ^ (string_of_int c.idx)
  | Interpolant -> "IP_" ^ (string_of_int c.idx)
  | Constant -> "CON_" ^ (string_of_int c.idx)
  | EqTest -> "EQTEST_" ^ (string_of_int c.idx)
  | Axiom s -> "AXIOM_" ^ s
  | Summary _ -> failwith "should not be asserting summaries"

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

let compare_tid_opt a b = 
  try 
    let tidA = extract_tid a in
    let tidB = extract_tid b in
    Some (compare tidA tidB)
  with
    _ -> None

let extract_group cls = 
  let rec aux = function
    | [] -> failwith "no tid"
    | x::xs ->  match x with
      | SummaryGroupTag i -> i
      | _ -> aux xs
  in
  aux cls.cTags

let clause_defines cls v = SSAVarSet.mem v cls.defs

let get_uses clause = SSAVarSet.diff clause.ssaVars clause.defs
let all_ssaVars clauses = List.fold_left (fun a e -> SSAVarSet.union e.ssaVars a) SSAVarSet.empty clauses
let all_basevars clauses = 
  let allVars = all_ssaVars clauses in
  SSAVarSet.fold (fun e a -> BaseVarSet.add e.vidx a) allVars BaseVarSet.empty

let print_ssa_map map = 
  print_endline "id\tname\tdefloc";
  VarSSAMap.iter
    (fun k v -> 
      Printf.printf "%d\t%s\t%d\n" 
	k 
	v.fullname 
        (get_location_line v))
    map
