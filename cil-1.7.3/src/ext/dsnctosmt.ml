open Dsnsmtdefs
(*open Dsnsmt*)
open Cil
open Dsnutils

(* DSN TODO just pass this around *)
type smtParsedResults = 
  { count : int;
    typeMap: varTypeMap;
    seenThreads : TIDSet.t;
    seenGroups : GroupSet.t;
    clauses : clause list;
    (*mutable graph : Dsngraph.G.t option;*)
  }

type smtParseInternal = {
  mutable currentFunc: string;
  mutable revProgram: clause list;
  mutable currentIfContext : ifContextList;
  mutable currentThread : int option;
  mutable currentLabel : string option;
  mutable currentGroup : int option;
}

(******************** Globals *************************)
let currentFunc: string ref = ref ""
(*keep the program in reverse order, then flip once. Avoid unneccessary list creation*)
let revProgram : clause list ref = ref [] 
let currentIfContext : ifContextList ref = ref Dsnsmt.emptyIfContext
let currentThread : int option ref = ref None
let currentLabel : string option ref = ref None
let currentGroup : int option ref = ref None
let seenThreads = ref TIDSet.empty
let seenGroups = ref GroupSet.empty

let get_ssa_before () = 
  match !revProgram with
  | [] -> emptySSAMap
  | x::xs -> x.ssaIdxs

(*********************************C to smt converstion *************************************)
let formula_from_lval l = 
  match l with 
  | (Var(v),_) -> SMTSsaVar(smtSsaVarFromString(v.vname))
  | _ -> failwith "should only have lvals of type var"

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
  | BAnd | BXor | BOr| Shiftlt | Shiftrt -> 
    failwith "not supporting bit operators"
  | _ -> failwith ("unexpected operator in smtopfrombinop |" 
		   ^ (d_string "%a" d_binop op ) ^ "|")
    

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

(***************************** Parse file to smt ******************************)

(* we assume that the thread mentioned in the label is good until the next label
 * this requires that we use --keepunused to keep the labels active *)
let parseLabel s = 
  match s.labels with
  | [] -> ()
  | [Label(s,l,b)] -> begin
    if not (begins_with s "VERMEER__") then begin
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
  end
  | _ -> failwith ("unexpected label " ^ d_labels s.labels)

(* Future work - capture the global variables inside an object. then
 * we can just pass that around *)
class dsnsmtVisitorClass = object
  inherit Cil.nopCilVisitor

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
      let cls = Dsnsmt.make_clause assgt ssaBefore !currentIfContext (ProgramStmt (i,!currentThread)) tags in
      revProgram := cls :: !revProgram;
      DoChildren
    | Call(lo,e,al,l) ->
      assert_is_assert i;
      let form = match al with 
	| [x] -> formula_from_exp x
	| _ -> failwith "assert should have exactly one element"
      in
      let cls = Dsnsmt.make_clause form ssaBefore !currentIfContext (ProgramStmt (i,!currentThread)) tags in
      revProgram := cls :: !revProgram;
      DoChildren
    | _ -> DoChildren
  end
  method vstmt (s : stmt) = begin
    parseLabel s;
    match s.skind with
    | If(i,t,e,l) ->
      if e.bstmts <> [] then failwith "else block not handeled";
      let cond = Dsnsmt.type_check_and_cast_to_bool (formula_from_exp i) in
      currentIfContext := {iformula = cond; istmt = s} :: !currentIfContext;
      ChangeDoChildrenPost (s,
			    fun x -> 
			      currentIfContext := List.tl !currentIfContext;
			      x)
    | Block _ -> DoChildren
    | _ -> DoChildren
  end
end

let parse_file (file: file) = 
  let dsnsmtVisitor = new dsnsmtVisitorClass in
  let doGlobal = function 
    | GVarDecl (v, _) -> ()
    | GFun (fdec, loc) ->
      currentFunc := fdec.svar.vname;
      (* do the body *)
      ignore (visitCilFunction dsnsmtVisitor fdec);
    | _ -> () in 
  let _ = Stats.time "dsn" (iterGlobals file) doGlobal in
  let clauses = List.rev !revProgram in
  {count = !Dsnsmt.count;
   typeMap = !Dsnsmt.typeMap;
   seenGroups = !seenGroups;
   seenThreads = !seenThreads;
   clauses = clauses;
  }
