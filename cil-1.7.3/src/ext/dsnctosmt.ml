open Dsnsmtdefs
(*open Dsnsmt*)
open Cil
open Dsnutils

type smtParseInternal = {
  mutable currentFunc: string;
  (*keep the program in reverse order, then flip once. Avoid unneccessary list creation*)
  mutable currentRevProgram: clause list;
  mutable currentIfContext : ifContextList;
  mutable currentThread : int option;
  mutable currentLabel : string option;
  mutable currentGroup : int option;
  mutable currentSeenThreads : TIDSet.t;
  mutable currentSeenGroups : TIDSet.t;
}

let initialCtoSMT () = {
  currentFunc = "";
  currentRevProgram = [];
  currentIfContext = [];
  currentThread = None;
  currentLabel = None; 
  currentGroup = None;
  currentSeenThreads = TIDSet.empty;
  currentSeenGroups = TIDSet.empty;
}

(* internal globals *)
let ig = initialCtoSMT ()

(******************** Globals *************************)

let get_ssa_before () = 
  match ig.currentRevProgram with
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
	ig.currentSeenThreads <- TIDSet.add newThread ig.currentSeenThreads;
	ig.currentThread <- Some (newThread);
	ig.currentLabel <- Some(s);
	ig.currentSeenThreads <- GroupSet.add newGroup ig.currentSeenGroups;
	ig.currentGroup <- Some(newGroup)
      | _ -> failwith ("bad label string " ^ s)
    end
  end
  | _ -> failwith ("unexpected label " ^ d_labels s.labels)

(* Future work - capture the global variables inside an object. then
 * we can just pass that around *)
class dsnsmtVisitorClass ig = object (self)
  inherit Cil.nopCilVisitor

  method vinst i = begin
    let tags = match ig.currentThread with
      | Some (tid) -> [ThreadTag tid]
      | None -> [] in
    let tags = match ig.currentLabel with
      | Some l -> (LabelTag l)::tags
      | None -> tags in
    let tags = match ig.currentGroup with
      | Some g -> SummaryGroupTag g :: tags
      | None -> tags in
    let ssaBefore = get_ssa_before () in
    match i with
    |  Set(lv, e, l) -> 
      let lvForm = formula_from_lval lv in
      let eForm = formula_from_exp e in
      let assgt = SMTRelation("=",[lvForm;eForm]) in
      let cls = Dsnsmt.make_clause assgt ssaBefore ig.currentIfContext 
	(ProgramStmt (i,ig.currentThread)) tags in
      ig.currentRevProgram <- cls :: ig.currentRevProgram;
      DoChildren
    | Call(lo,e,al,l) ->
      assert_is_assert i;
      let form = match al with 
	| [x] -> formula_from_exp x
	| _ -> failwith "assert should have exactly one element"
      in
      let cls = Dsnsmt.make_clause form ssaBefore ig.currentIfContext 
	(ProgramStmt (i,ig.currentThread)) tags in
      ig.currentRevProgram <- cls :: ig.currentRevProgram;
      DoChildren
    | _ -> DoChildren
  end
  method vstmt (s : stmt) = begin
    parseLabel s;
    match s.skind with
    | If(i,t,e,l) ->
      if e.bstmts <> [] then failwith "else block not handeled";
      let cond = Dsnsmt.type_check_and_cast_to_bool (formula_from_exp i) in
      ig.currentIfContext <- {iformula = cond; istmt = s} :: ig.currentIfContext;
      ChangeDoChildrenPost (s,
			    fun x -> 
			      ig.currentIfContext <- List.tl ig.currentIfContext;
			      x)
    | Block _ -> DoChildren
    | _ -> DoChildren
  end
end

let parse_file (file: file) ?(dottyFileName = None) makeGraph = 
  let dsnsmtVisitor = new dsnsmtVisitorClass ig in
  let doGlobal = function 
    | GVarDecl (v, _) -> ()
    | GFun (fdec, loc) ->
      ig.currentFunc <- fdec.svar.vname;
      (* do the body *)
      ignore (visitCilFunction dsnsmtVisitor fdec);
    | _ -> () in 
  let _ = Stats.time "dsn" (iterGlobals file) doGlobal in
  let clauses = List.rev ig.currentRevProgram in
  let graph = if makeGraph 
    then Some (Dsngraph.make_dependency_graph ~dottyFileName:dottyFileName clauses) 
    else None in
  let open Dsnsmt in
  {
    typeMap = !Dsnsmt.typeMap;
    seenGroups = ig.currentSeenGroups;
    seenThreads = ig.currentSeenThreads;
    clauses = clauses;
    graph = graph;
  }
