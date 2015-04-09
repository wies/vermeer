open Dsnsmtdefs
(*open Dsnsmt*)
open Cil
open Dsnutils

module SMT = SmtSimpleAst

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
let get_lhs_var = function
  | (Var(v),_) -> v.vname
  | _ -> failwith "should only have lvals of type var"
    
  
let smtOpFromBinop = function
  | PlusA -> SMT.Add
  | Mult -> SMT.Mult
  | LAnd -> SMT.And
  | LOr -> SMT.Or
  | Eq -> SMT.Eq
  | Ne -> SMT.Neq
  | Lt -> SMT.Lt
  | Le -> SMT.Leq
  | Gt -> SMT.Gt
  | Ge -> SMT.Geq
  | PlusPI|IndexPI|MinusA|MinusPI|MinusPP|Div|Mod|Shiftlt|Shiftrt|BAnd|BXor|BOr as op
    -> failwith ("unexpected operator in smtopfrombinop |"
    		 ^ (d_string "%a" d_binop op ) ^ "|")
    

let formula_from_exp typeMap e =
  let formula_from_lval l = 
    match l with 
    | (Var(v),_) -> SMT.mk_ident v.vname (typeMap v.vname)
    | _ -> failwith "should only have lvals of type var"
  in
  let rec aux = function
  | Const(CInt64(c,_,_)) -> SMT.mk_intConst c
  | Const(CChr(c)) -> SMT.mk_intConst (Int64.of_int (int_of_char c))
  | Const(_) as f -> failwith (d_string "Constants should only be of type int: %a" d_exp f)
  | Lval(l) -> formula_from_lval l 
  | UnOp(Neg,e1,t) -> SMT.mk_uminus (aux e1)
  | UnOp (o,_,_) -> failwith (d_string "unexpected unop  %a" d_unop o)
  | BinOp(o,e1,e2,t) ->SMT.mk_rel (smtOpFromBinop o) (aux e1) (aux e2) 
  | CastE(t,e) -> aux e
  | SizeOf _|SizeOfE _|SizeOfStr _|AlignOf _|AlignOfE _|Question (_, _, _, _)
  | AddrOf _|AddrOfLabel _|StartOf _ as f
    -> failwith (d_string "Unexpected expression %a in %a" d_exp f d_exp e) 
  in 
  aux e
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
	ig.currentSeenGroups <- GroupSet.add newGroup ig.currentSeenGroups;
	ig.currentGroup <- Some(newGroup)
      | _ -> failwith ("bad label string " ^ s)
    end
  end
  | _ -> failwith ("unexpected label " ^ d_labels s.labels)

let register_lval_location lval location = 
  smtVarDefLoc := SSAVarMap.add (ssaVarFromString lval) location !smtVarDefLoc

let register_type v t = Dsnsmt.set_var_type v t
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
      let rhsForm = formula_from_exp Dsnsmt.get_var_type e in
      let sort = SMT.get_sort rhsForm in
      let lhsVar = get_lhs_var lv in
      let lhsForm = SMT.mk_ident lhsVar sort in
      register_lval_location lhsVar l;
      register_type lhsVar sort;
      let assgt = SMT.mk_eq lhsForm rhsForm in 
      let cls = Dsnsmt.make_clause assgt ssaBefore ig.currentIfContext 
	(ProgramStmt (i,ig.currentThread)) tags in
      ig.currentRevProgram <- cls :: ig.currentRevProgram;
      DoChildren
    | Call(lo,e,al,l) ->
      assert_is_assert i;
      let form = match al with 
	| [x] -> formula_from_exp Dsnsmt.get_var_type  x 
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
      let cond = SMT.cast_to_bool (formula_from_exp  Dsnsmt.get_var_type i) in
      ig.currentIfContext <- {iformula = cond; istmt = s} :: ig.currentIfContext;
      ChangeDoChildrenPost (s,
			    fun x -> 
			      ig.currentIfContext <- List.tl ig.currentIfContext;
			      x)
    | Block _ -> DoChildren
    | _ -> DoChildren
  end
end

let parse_file (file: file)h = 
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
  Dsnsmt.setSmtContext
    ("initialParse" ^ file.fileName)
    ig.currentSeenGroups
    ig.currentSeenThreads
    clauses
    
