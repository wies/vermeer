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

type sexpType = | Sexp 
		| SexpRel 
		| SexpLet
		| SexpIntConst 
		| SexpBoolConst
		| SexpSsaVar of smtSsaVar 
		| SexpLetVar 
		| SexpFlagVar 

type ifContextElem = {iformula : term; istmt : Cil.stmt}
type ifContextList = ifContextElem list

type clauseTag = ThreadTag of int | LabelTag of string | SummaryGroupTag of int
let noTags = []

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
