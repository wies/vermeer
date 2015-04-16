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

(* in 4.02, I can use shorter names as good aliases *)
module SMTFn = SmtSimpleFns
module SB = SmtSimpleAstBuilder
module VarSet = SmtSimpleAst.VarSet
module Parser = SmtLibParser
module SolverAST = SmtLibSyntax

type smtOpts = 
  {
    mutable beautifyFormulas : bool;
  }

let opts = {
  beautifyFormulas = false;
}

let string_of_exn = function 
  | ProgError.Prog_error _ as e ->
    ProgError.to_string e ^ "\n" ^  Printexc.get_backtrace ()
  | x -> Printexc.to_string x ^ "\n" ^ Printexc.get_backtrace ()

(* issue if interpolant tries to go past where something is used *)

let (get_var_type, set_var_type) = 
  let typeMap = ref SmtSimpleAst.VarSortMap.empty in
  (
    (fun v -> 
      if (is_flag_var v) then SmtSimpleAst.BoolSort
      else if (is_ssa_var v) then 
	SmtSimpleAst.VarSortMap.find v !typeMap
      else failwith ("Cannot find type for " ^ v)
    ),
    (fun v sort -> 
      typeMap := SmtSimpleAst.VarSortMap.add v sort !typeMap
    )
  )

module HazardSet = Dsngraph.HazardSet

(* DSN TODO just pass this around *)
type smtContext = 
  {
    contextName : string;
    seenThreads : TIDSet.t;
    seenGroups : GroupSet.t;
    clauses : clause list;
    graph : Dsngraph.G.t option; (*lazy var *)
  }

(* a bit of a hack - yet another global :( *)
let makeDottyFiles = ref false
(* typemap should go in here too *)
let privateSmtContext = ref {
  contextName = "ERROR.  EMPTY.";
  seenThreads = TIDSet.empty;
  seenGroups = GroupSet.empty;
  clauses = [];
  graph = None;
}

(* should only ever update it using this fn *)
let setSmtContext name seenThreads seenGroups clauses = 
  privateSmtContext :=
    {
      contextName = name;
      seenThreads = seenThreads;
      seenGroups = seenGroups;
      clauses = clauses;
      graph = None;
    }

let getCurrentSeenThreads () =  !privateSmtContext.seenThreads
let getCurrentSeenGroups() =  !privateSmtContext.seenGroups
let getCurrentClauses () =  !privateSmtContext.clauses
let getCurrentGraph ?(make) () = 
  match !privateSmtContext.graph with
  | Some g -> g 
  | None ->   
    let dottyFileName = 
      if !makeDottyFiles then Some !privateSmtContext.contextName else None in
    let graph = Dsngraph.make_dependency_graph 
      ~dottyFileName:dottyFileName (getCurrentClauses()) in
    privateSmtContext := {!privateSmtContext with graph = Some graph};
    graph

let rec make_ssa_map (vars : ssaVar list) (ssaMap : varSSAMap) (defs : SSAVarSet.t) 
    : (varSSAMap * SSAVarSet.t) =
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
      else (VarSSAMap.add vidx v ssaMap, SSAVarSet.add v defs) in 
    make_ssa_map  vs ssaMap defs
      
(* this rebuilds the clauses, and the graph.  DO NOT USE THE OLD 
 * CLAUSES OR GRAPH AFTER THIS POINT *)
let topoSortCurrent () = 
  let remake_ssa_map clauses = 
    let (_,newClausesRev) = 
      List.fold_left 
	(fun (ssaBefore,revClsLst) cls -> 
	  let v = cls.ssaVars in
	  let (newSsa,newDefs) = 
	    make_ssa_map (SSAVarSet.elements v) ssaBefore SSAVarSet.empty in
	  (newSsa,{cls with ssaIdxs = newSsa}::revClsLst)) 
	(VarSSAMap.empty,[]) clauses in
    List.rev newClausesRev
  in
  let newClauses = Dsngraph.topo_sort_graph (getCurrentGraph()) in
  let newClauses = remake_ssa_map newClauses in
  privateSmtContext := {
    !privateSmtContext with 
      contextName = "post_topo_sort";
      clauses = newClauses; 
      graph = None;
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
		| SexpSsaVar of ssaVar 
		| SexpLetVar 
		| SexpFlagVar 

(******************** Defs *************************)
let smtDir = "./smt/"
let smtCheckSat = "(check-sat)\n"
let smtGetUnsatCore = "(get-unsat-core)\n"

let smtZero = SmtSimpleAst.zero
let smtOne = SmtSimpleAst.one
let emptyIfContext = []

(******************** Globals *************************)

let get_new_clause_id = 
  let count = ref 0 in
  fun () -> incr count; !count

let trace_from_at at = 
  let interpolants,trace = List.split at in 
  trace
    
let do_on_trace fn at = fn (trace_from_at at)


(******************** Print Functions *************************)
let string_of_var v = v.fullname

let rec string_of_formula (f : SmtSimpleAst.term) : string = 
  SmtSimpleFns.string_of_term f
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

(* could make tail rec if I cared *)
let debug_SSAMap m = 
  let string_of_binding (k,v) = "\t(" ^ string_of_int k ^ ", " ^ debug_var v ^ ")\n" 
  in List.fold_left (fun a e -> (string_of_binding e) ^ a) "" (VarSSAMap.bindings m)

let debug_vars vars = 
  List.fold_left (fun a e -> "\t" ^ debug_var e ^ "\n" ^ a) "" (SSAVarSet.elements vars)
    

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
  | [x] -> SB.mk_impl x formula
  | _ ->  SB.mk_impl (SB.mk_and dependencyList) formula 

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
let get_flag_var c = SB.mk_ident (flag_var_string c) SmtSimpleAst.BoolSort

let make_flag clause formula = 
  match clause.typ with 
  | ProgramStmt _ ->  SB.mk_and [formula;get_flag_var clause]
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
  form    
    
let make_var_decl v =
  let ts = SmtSimpleAst.string_of_sort (get_var_type v) in 
  "(declare-fun " ^ (SmtSimpleAst.string_of_var v)  ^" () " ^ ts ^ ")\n"  

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

let fold_ssa_vars formula initialSet = 
  let all_vars = SmtSimpleFns.get_idents formula in
  SmtSimpleAst.VarSet.fold 
    (fun e a -> match ssaVarOptFromString e with
    | Some v -> SSAVarSet.add v a
    | None -> a)  
    all_vars initialSet
    
let get_ssa_vars formula = fold_ssa_vars formula SSAVarSet.empty

  
(****************************** Clauses ******************************)
(* two possibilities: either maintain a mapping at each point
 * or remap as we go starting from one end *)


(* So we need to figure out the type of each variable *)



(* this function does two things: It determines the type of the 
 * expression.  It also updates the mapping with any newly discovered
 * var -> type mappings
 *)
let get_ssa_vars_ic icList = 
  List.fold_left (fun a e -> fold_ssa_vars e.iformula a) SSAVarSet.empty icList


let count_basevars clauses = 
  BaseVarSet.cardinal (all_basevars clauses)

let count_basevars_at a = count_basevars (trace_from_at a)

(* the first time we see a new index, we know we have a defn for it *)
let make_clause (f: term) (ssa: varSSAMap) (ic : ifContextList) 
    (ct: clauseType) (tags : clauseTag list)
    : clause = 
  let rec make_ssa_map (vars : ssaVar list) (ssaMap : varSSAMap) (defs : SSAVarSet.t) 
      : (varSSAMap * SSAVarSet.t) =
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
	else (VarSSAMap.add vidx v ssaMap, SSAVarSet.add v defs)
      in
      make_ssa_map vs ssaMap defs 
  in
  let ssaVars = get_ssa_vars f in
  let icSsaVars = get_ssa_vars_ic ic in
  let allSSAVars = SSAVarSet.union ssaVars icSsaVars in
  let ssa,defs  = make_ssa_map (SSAVarSet.elements allSSAVars) ssa SSAVarSet.empty in
  let f = SmtSimpleAstBuilder.cast_to_bool f in
  let f = if opts.beautifyFormulas then SmtSimplePasses.beautify_formula f else f in
  {formula = f; 
   idx = get_new_clause_id(); 
   ssaVars = allSSAVars; 
   defs = defs;
   ssaIdxs = ssa; 
   typ = ct; 
   ifContext = ic;
   cTags = tags
  } 

let make_true_clause () = make_clause SB.mk_true emptySSAMap emptyIfContext Constant noTags
let make_false_clause () =  make_clause SB.mk_false emptySSAMap emptyIfContext Constant noTags
let negate_clause cls = {cls with formula = SB.mk_not cls.formula}


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
  let remap_var str = 
    let oldSsaVar = ssaVarFromString str in
    let newVarOpt = get_current_var oldSsaVar ssaMap in
    match newVarOpt with
    | Some (newVar) -> newVar.fullname
    | None -> raise (CantMap oldSsaVar)
  in
  let rec aux = function 
    | SmtSimpleAst.Ident (v,s) when is_ssa_var v -> SB.mk_ident (remap_var v) s
    | SmtSimpleAst.BoolConst _ | SmtSimpleAst.IntConst _ | SmtSimpleAst.Ident _ as f -> f
    | SmtSimpleAst.App (o,tl,s) -> SB.mk_app o (List.map aux tl)
    | SmtSimpleAst.LinearRelation(o,tl,v) ->
      (* we should only have SSA Vars in these relations *)
      SB.mk_linearRelation o (List.map (fun (c,v) -> (c,remap_var v)) tl) v
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


let extract_unsat_core (str) : string list = 
  let str = strip_parens str in
  Str.split (Str.regexp "[ \t]+") str

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

let solver_options = function
  | CheckSat -> 
    ["print-success",false; "produce-proofs",false; "produce-unsat-cores", false]
  | GetUnsatCore -> 
    ["print-success",false; "produce-proofs",true; "produce-unsat-cores", true]
  | GetInterpolation -> 
    ["print-success",false; "produce-proofs",true; "produce-unsat-cores", false]

let smtinterpol_2_1 = 
  let basedir = get_basedir () in
  let jarfile = basedir ^ "/smtinterpol/smtinterpol.jar" in
  { 
    version = 2; 
    subversion = 1;
    has_set_theory = false;
    smt_options = solver_options CheckSat;
    kind = Process("java",["-jar";jarfile;"-q"]);
  }
    
(* assume that z3 is on the path *)
let z3_4_3 = 
  { 
    version = 4; 
    subversion = 3;
    has_set_theory = false;
    smt_options = solver_options CheckSat;
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
    mutable isSat : bool option;
    mutable solverOpts : (string * bool) list;
    mutable assertions : SmtSimpleAst.assertion list;
    mutable vars : VarSet.t;
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
  let set_option ((opt_name,opt_value) as opt) =
    let optStr = Printf.sprintf "(set-option :%s %b)\n" opt_name opt_value in
    solver.solverOpts <- opt::solver.solverOpts;
    write_line_to_solver solver optStr
  in
  List.iter set_option opts

let set_timeout solver timeout = 
  write_line_to_solver solver ("(set-option :timeout " ^ string_of_int timeout ^ ")\n")

let set_logic solver logic = write_line_to_solver solver ("(set-logic " ^ logic ^ ")\n")
let declare_unknown_sort solver = write_line_to_solver solver "(define-sort Unknown () Int)\n"
  
let reset_solver solver = 
  solver.isSat <- None;
  solver.solverOpts <- [];
  solver.assertions <- [];
  solver.vars <- VarSet.empty;
  write_line_to_solver solver "(reset)\n"

let read_from_solver solver =
  match SmtLibSolver.read_from_chan solver.in_chan with
  | SolverAST.Sat -> Sat
  | SolverAST.Unsat -> Unsat
  | SolverAST.Unknown -> failwith "got parser unknown"
  | SolverAST.Model cl -> failwith "not currently supporting models"
  | SolverAST.Interpolant tl -> 
    let i = List.map (SmtSimplifierLibConverter.smtSimpleofSmtLib get_var_type) tl in
    let i = if opts.beautifyFormulas 
      then List.map 
	(fun x -> 
	  Printf.printf "Old was: %s\n"  (SmtSimpleFns.string_of_term x);
	  let n = SmtSimplePasses.beautify_formula x in
	  Printf.printf "New was: %s\n"  (SmtSimpleFns.string_of_term n);
	  n) i 
      else i in
    Interpolant i
  | SolverAST.UnsatCore sl -> 
    UnsatCore (List.fold_left (fun a e -> StringSet.add e a) StringSet.empty sl)
  | SolverAST.SingleTerm t -> failwith "did not expect to get a single term"
  | SolverAST.Error s -> failwith ("parser error " ^ s)


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
	  isSat = None;
	  assertions = [];
	  solverOpts = [];
	  vars = VarSet.empty;
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

let declare_var solver v =
  if (not (VarSet.mem v solver.vars)) then (
    solver.vars <- VarSet.add v solver.vars;
    write_line_to_solver solver (make_var_decl v)
  )

let assertion_of_clause c = 
  SmtSimpleFns.assertion_of_formula (clause_name c) (encode_formula currentEncoding c)

let assert_assertion solver a = 
  solver.assertions <- a:: solver.assertions;
  solver.isSat <- None;
  write_line_to_solver solver (SMTFn.string_of_assertion a)


(* given a set of clauses, do what is necessary to turn it into smt queries *)
let program_to_smt solver clauses opts =
  reset_solver solver;
  set_solver_options solver opts;
  set_logic solver "QF_LIA";
  let encodedAssertions = List.map assertion_of_clause clauses in 
  let allIdents = List.fold_left 
    (fun a (_,_,idents) -> VarSet.union idents a) VarSet.empty encodedAssertions in
  VarSet.iter (declare_var solver) allIdents;
  (* write the assertions *)
  List.iter (assert_assertion solver) encodedAssertions;
  flush_solver solver

let get_solver_for = function
  | CheckSat | GetUnsatCore -> getZ3 ()
  | GetInterpolation -> getSmtinterpol()
    

let was_sat solver =
  match solver.isSat with
  | Some s -> s 
  | None -> ( 
    write_line_to_solver solver smtCheckSat;
    flush_solver solver;
    let result = match read_from_solver solver with
      | Sat -> true 
      | Unsat -> false 
      | _ -> failwith "expected either sat or unsat"
    in
    solver.isSat <- Some result;
    result
  )

let was_unsat solver = not (was_sat solver)

let check_sat clauses = 
  let solver = get_solver_for CheckSat in
  program_to_smt solver clauses (solver_options CheckSat);
  was_sat solver

let check_unsat clauses = not (check_sat clauses)

(* DSN TODO clean this up *)
let get_interpolant clauses partition = 
  let solver = get_solver_for GetInterpolation in
  program_to_smt solver clauses (solver_options GetInterpolation);
  if (was_unsat solver) then (
    write_line_to_solver solver partition;
    flush_solver solver;
    match read_from_solver solver with
    | Interpolant _ as f -> f
    | _ -> failwith "not an interpolant"
  ) else 
    failwith "Tried to get an interpolant, but was sat"


let get_unsat_core clauses = 
  let solver = get_solver_for GetUnsatCore in
  program_to_smt solver clauses (solver_options GetUnsatCore);
  if (was_unsat solver) then (
    write_line_to_solver solver smtGetUnsatCore;
    flush_solver solver;
    match read_from_solver solver with
    | UnsatCore _ as f -> f
    | _ -> failwith "not an interpolant"
  ) else 
    failwith "Tried to get an unsatcore, but was sat"

let are_interpolants_equiv (i1 :term) (i2 :term)= 
  (* interpolants have no need for ssa variables.  So we can just drop them *)
  let rec ssa_free_interpolant = function 
    | SmtSimpleAst.Ident (v,s) when is_ssa_var v -> SB.mk_ident (remap_ssa_var_str v 0) s
    | SmtSimpleAst.BoolConst _ | SmtSimpleAst.IntConst _  | SmtSimpleAst.Ident _ as f-> f
    | SmtSimpleAst.App(o,tl,s) -> SB.mk_app o (List.map ssa_free_interpolant tl)
    | SmtSimpleAst.LinearRelation (o,lhs,rhs) ->  
      SB.mk_linearRelation o (List.map (fun (c,v) -> (c,remap_ssa_var_str v 0)) lhs) rhs
  in
  let i1form = ssa_free_interpolant i1 in
  let i2form = ssa_free_interpolant i2 in
  if i1form = i2form then true 
  else 
    let equiv = SB.mk_rel SmtSimpleAst.Neq i1form i2form in 
    let cls = make_clause equiv emptySSAMap emptyIfContext EqTest noTags in 
    check_unsat [cls]

let is_valid_interpolant (before :clause list) (after : clause list) (inter :clause) = 
  let not_inter = negate_clause inter in
  (check_unsat (not_inter :: before)) && (check_unsat (inter :: after))

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

