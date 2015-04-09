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

module SMT = SmtSimpleAst
module Parser = SmtLibParser

(* just make it compile smtlib.  Testing purposes only *)
type foobar = SmtLibSyntax.sort
let barfoo = Smtlib_main.run
let baz = SmtLibSimplifierConverter.smtCore_of_smtSimple
(* issue if interpolant tries to go past where something is used *)

let (get_var_type, set_var_type) = 
  let typeMap = ref SMT.VarSortMap.empty in
  (
    (fun v -> 
      if (is_flag_var v) then SMT.BoolSort
      else if (is_ssa_var v) then 
	SMT.VarSortMap.find v !typeMap
      else failwith ("Cannot find type for " ^ v)
    ),
    (fun v sort -> 
      typeMap := SMT.VarSortMap.add v sort !typeMap
    )
  )

let smtCallTime = ref []

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
	  let v = cls.vars in
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

let smtZero = SMT.zero
let smtOne = SMT.one
let emptyIfContext = []

(******************** Globals *************************)

let count = ref 1

let trace_from_at at = 
  let interpolants,trace = List.split at in 
  trace
    
let do_on_trace fn at = fn (trace_from_at at)


(******************** Print Functions *************************)
let string_of_var v = v.fullname

let rec string_of_formula (f : SMT.term) : string = failwith "not implemented"
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
  | [x] -> SMT.mk_impl x formula
  | _ ->  SMT.mk_impl (SMT.mk_and dependencyList) formula 

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
let get_flag_var c = SMT.mk_ident (flag_var_string c) SMT.BoolSort

let make_flag clause formula = 
  match clause.typ with 
  | ProgramStmt _ ->  SMT.mk_and [formula;get_flag_var clause]
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
  "(assert (! " 
  ^ string_of_formula form
  ^ " :named " ^ clause_name clause
  ^ "))\n"
    
    
let make_var_decl v =
  failwith "todo later"
  (* let ts = SMT.string_of_sort (get_var_type v) in *)
  (* "(declare-fun " ^ (string_of_var v)  ^" () " ^ ts ^ ")\n"  *)


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
  let all_vars = SMT.get_idents formula in
  SMT.VarSet.fold (fun e a -> match ssaVarOptFromString e with
  | Some v -> SSAVarSet.add v a
  | None -> a)  all_vars initialSet

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
  incr count;
  let ssaVars = get_ssa_vars f in
  let icSsaVars = get_ssa_vars_ic ic in
  let allSSAVars = SSAVarSet.union ssaVars icSsaVars in
  let ssa,defs  = make_ssa_map (SSAVarSet.elements allSSAVars) ssa SSAVarSet.empty in
  let f = SMT.cast_to_bool f in
  {formula = f; 
   idx = !count; 
   vars = allSSAVars; 
   defs = defs;
   ssaIdxs = ssa; 
   typ = ct; 
   ifContext = ic;
   cTags = tags
  } 

let make_true_clause () = make_clause SMT.mk_true emptySSAMap emptyIfContext Constant noTags
let make_false_clause () =  make_clause SMT.mk_false emptySSAMap emptyIfContext Constant noTags
let negate_clause cls = {cls with formula = SMT.mk_not cls.formula}


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
    | SMT.Ident (v,s) when is_ssa_var v -> SMT.mk_ident (remap_var v) s
    | SMT.BoolConst _ | SMT.IntConst _ | SMT.Ident _ as f -> f
    | SMT.App (o,tl,s) -> SMT.mk_app o (List.map aux tl)
    | SMT.LinearRelation(o,tl,v) ->
      (* we should only have SSA Vars in these relations *)
      SMT.mk_linearRelation o (List.map (fun (c,v) -> (c,remap_var v)) tl) v
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

let unsatCoreOptions =  
  ["print-success",false; "produce-proofs",true; "produce-unsat-cores", true]
let interpolationOptions = 
  ["print-success",false; "produce-proofs",true; "produce-unsat-cores", false]
let smtOnlyOptions = 
  ["print-success",false; "produce-proofs",false; "produce-unsat-cores", false]

let smtinterpol_2_1 = 
  let basedir = get_basedir () in
  let jarfile = basedir ^ "/smtinterpol/smtinterpol.jar" in
  { 
    version = 2; 
    subversion = 1;
    has_set_theory = false;
    smt_options = smtOnlyOptions;
    kind = Process("java",["-jar";jarfile;"-q"]);
  }
    
(* assume that z3 is on the path *)
let z3_4_3 = 
  { 
    version = 4; 
    subversion = 3;
    has_set_theory = false;
    smt_options = smtOnlyOptions;
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
  let set_option (opt_name,opt_value) =
    let optStr = Printf.sprintf "(set-option :%s %b)\n" opt_name opt_value in
    write_line_to_solver solver optStr
  in
  List.iter set_option opts

let set_timeout solver timeout = 
  write_line_to_solver solver ("(set-option :timeout " ^ string_of_int timeout ^ ")\n")

let set_logic solver logic = write_line_to_solver solver ("(set-logic " ^ logic ^ ")\n")
let declare_unknown_sort solver = write_line_to_solver solver "(define-sort Unknown () Int)\n"
  
let reset_solver solver = write_line_to_solver solver "(reset)\n"

let read_from_chan chan =
  let lexbuf = Lexing.from_channel chan in
  (* This is useful for debugging, but not necessary *)
  (*SmtLibLexer.set_file_name lexbuf session.log_file_name; *)
  SmtLibParser.output SmtLibLexer.token lexbuf

let line_from_solver solver = 
  let line = input_line solver.in_chan in
  debug_endline line;
  line

let read_from_solver solver =
  match read_from_chan solver.in_chan with
  | _ -> failwith "foo"
  (* | Parser.Sat  *)
  (* | Parser.Unsat *)
  (* | Parser.Unknown *)
  (* | Parser.Model of command list *)
  (* | Parser.Interpolant of command list *)
  (* | Parser.UnsatCore sl ->  *)
  (* | Parser.Error s -> failwith ("parser error " ^ s) *)


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

(* given a set of clauses, do what is necessary to turn it into smt queries *)
let _do_smt ?(justPrint = false) solver clauses pt =
  (* print_endline "doing smt"; *)
  reset_solver solver;
  let opts = match pt with 
    | CheckSat -> smtOnlyOptions
    | GetUnsatCore -> unsatCoreOptions 
    | GetInterpolation _-> interpolationOptions 
  in 
  set_solver_options solver opts;
  set_logic solver "QF_LIA";
  (* on occation, there are variables that are never used in a way where their type matters
   * assume they're ints *)
  declare_unknown_sort solver;
  (*write the declerations *)
  let allVars = all_vars clauses in
  SSAVarSet.iter (fun v -> write_line_to_solver solver (make_var_decl v)) allVars;
  (* declare the flags vars *)
  (*this is a bit of a hack.  We should really only do this for the ones we need *)
  List.iter (fun c -> write_line_to_solver solver (make_flag_decl c)) 
    (getCurrentClauses());
  (* write the program clauses *)
  List.iter (fun x -> write_line_to_solver solver (encode_formula currentEncoding x)) clauses;
  (* write the commands *)
  let cmds = match pt with
    | CheckSat -> 
      [smtCheckSat]
    | GetInterpolation (partition) ->  
      [smtCheckSat;partition]
    | GetUnsatCore -> 
      [smtCheckSat; smtGetUnsatCore]
  in
  write_to_solver solver cmds;
  flush_solver solver;
  if justPrint then NoSMTResult 
  else read_from_solver solver 

let do_smt clauses pt =
  let solver = match pt with
    | CheckSat | GetUnsatCore -> getZ3 ()
    | GetInterpolation _ -> getSmtinterpol()
  in
  let res, duration = Dsnutils.time (fun () -> _do_smt solver clauses pt) () in
  smtCallTime := !smtCallTime @ [duration];
  debug_endline 
    ("No. calls=" ^ string_of_int (List.length !smtCallTime) 
     ^ ", Time_this=" ^ string_of_float duration
     ^ " Time_total=" ^ string_of_float (List.fold_left (+.) 0. !smtCallTime));
  res

let print_smt filenameOpt clauses pt = 
  match filenameOpt with
  | Some filename ->
    let oc = open_out (filename ^ ".smt2") in
    let solver = {
      in_chan = stdin;
      out_chan = oc;
      pid = 0;
      log_out = None} in
    ignore( _do_smt ~justPrint:true solver clauses pt);
    close_out oc;
  | None -> 
    let solver = {
      in_chan = stdin;
      out_chan = stdout;
      pid = 0;
      log_out = None;
    } in
    ignore(_do_smt ~justPrint:true solver clauses pt)


let are_interpolants_equiv (i1 :term) (i2 :term)= 
  (* interpolants have no need for ssa variables.  So we can just drop them *)
  let rec ssa_free_interpolant = function 
    | SMT.Ident (v,s) when is_ssa_var v -> SMT.mk_ident (remap_ssa_var_str v 0) s
    | SMT.BoolConst _ | SMT.IntConst _  | SMT.Ident _ as f-> f
    | SMT.App(o,tl,s) -> SMT.mk_app o (List.map ssa_free_interpolant tl)
    | SMT.LinearRelation (o,lhs,rhs) ->  
      SMT.mk_linearRelation o (List.map (fun (c,v) -> (c,remap_ssa_var_str v 0)) lhs) rhs
  in
  let i1form = ssa_free_interpolant i1 in
  let i2form = ssa_free_interpolant i2 in
  if i1form = i2form then true 
  else 
    let equiv = SMT.mk_rel SMT.Neq i1form i2form in 
    let cls = make_clause equiv emptySSAMap emptyIfContext EqTest noTags in 
    match (do_smt [cls] CheckSat) with
    | Sat -> false
    | Unsat _ -> true
    | Timeout -> false (* conservative on timeout *)
    | NoSMTResult -> failwith "trying to get result from smt logging call"

let is_valid_interpolant (before :clause list) (after : clause list) (inter :clause) = 
  let not_inter = negate_clause inter in
  match do_smt (not_inter :: before) CheckSat  with
  | NoSMTResult -> failwith "trying to get result from smt logging call"
  | Timeout -> false
  | Sat -> false
  | Unsat(_) -> 
    match do_smt (inter :: after) CheckSat with
    | NoSMTResult -> failwith "trying to get result from smt logging call"
    | Sat -> false
    | Unsat(_) -> true 
    | Timeout -> false


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

