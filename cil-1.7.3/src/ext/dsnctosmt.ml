open Dsnsmtdefs
open Dsnsmt
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
  {count = !count;
   typeMap = !typeMap;
   seenGroups = !seenGroups;
   seenThreads = !seenThreads;
   clauses = clauses;
  }
