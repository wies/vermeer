(*******************************TYPES *************************************)
open Dsnutils

type varOwner = | Thread of int 
		| Global

type smtVarType = SMTBool | SMTInt | SMTUnknown
    
type smtSsaVar = 
  {fullname : string; 
   vidx: int; 
   owner : int; 
   ssaIdx : int}

(* canonical format: x_vidx_ssaidx *)
let smtSsaVarFromString str = 
  match split_on_underscore str with
  | [prefix;vidxStr;ssaIdxStr] -> 
    if prefix <> "x" then failwith ("invalid prefix " ^ prefix);
    {fullname = str; 
     vidx = (int_of_string vidxStr);
     ssaIdx =  (int_of_string ssaIdxStr);
     owner = -1
    }
  | _ -> failwith ("variable " ^ str ^ "is not in the valid format")

    
module VarM = struct 
  type t = smtSsaVar
  let compare = Pervasives.compare end ;;
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
type varSSAMap = smtSsaVar VarSSAMap.t
type varTypeMap = smtVarType TypeMap.t
let emptySSAMap : varSSAMap = VarSSAMap.empty
let emptyTypeMap : varTypeMap = TypeMap.empty
let emptyVarSet = VarSet.empty
let emptyStringSet = StringSet.empty

(* A let can take a list of bindings that it applies
 * So we SMTLet which takes a list of SMTLetBindings, which are of the 
 * form (SMTLetVar, term)
 * Eventually, this should all be cleaned up by encoding the whole thing in
 * some proper grammer.
 *)
type term = | SMTRelation of string * term list
	    | SMTConstant of int64
	    | SMTSsaVar of smtSsaVar
	    | SMTFlagVar of string
	    | SMTLetVar of string
	    | SMTLetBinding of term * term 
	    | SMTLet of term list * term
	    | SMTTrue | SMTFalse


(* TODO record the program location in the programStmt *)
type clauseType = ProgramStmt of Cil.instr * int option 
		  | Interpolant | Constant | EqTest  
		  | Summary of  (Cil.instr * int option ) list


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
	       vars : VarSet.t;
	       defs : VarSet.t;
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

exception CantMap of smtSsaVar

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

let get_uses clause = VarSet.diff clause.vars clause.defs
let all_vars clauses = List.fold_left (fun a e -> VarSet.union e.vars a) emptyVarSet clauses
let all_basevars clauses = 
  let allVars = all_vars clauses in
  VarSet.fold (fun e a -> BaseVarSet.add e.vidx a) allVars BaseVarSet.empty
