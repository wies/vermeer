open Dsnsmt
open Graph
open Dsnutils
open Cil

(****************************** Globals and types ******************************)
type analysis = 
  UNSATCORE | LINEARSEARCH | BINARYSEARCH | WINDOW | NONINDUCTIVE | NOREDUCTION
let analysis = ref UNSATCORE (*default *)
let summarizeThread = ref false
type multithreadAnalysis = 
  ALLGROUPS | ALLTHREADS | ABSTRACTENV | NOMULTI | PARTITIONTID | PARTITIONGROUP
let multithread = ref NOMULTI
let printTraceSMT = ref false
let printReducedSMT = ref false
let toposortInput = ref false


(****************************** encoding rules ******************************)
let make_flowsensitive clause formula = 
  make_dependent_on (List.map (fun x -> x.iformula) clause.ifContext) formula

let make_flowsensitive_this_tid tid clause formula = 
  match clause.typ with
  | ProgramStmt(_,None) -> failwith "expected a tid here"
  | ProgramStmt(instr, Some thatTid) when thatTid <> tid ->
    identityEncodingFn clause formula
  | _ ->
    make_flowsensitive clause formula

module HazardSet = Dsngraph.HazardSet
let trackedHazards = ref HazardSet.empty
let addTrackedHazard hazard = trackedHazards := HazardSet.add hazard !trackedHazards

let make_hazards graph hazards clause formula = 
  if HazardSet.is_empty hazards then 
    formula 
  else begin
    let hazard_preds = Dsngraph.get_hazard_preds graph hazards clause in
    let pred_flags = Dsngraph.ClauseSet.fold (fun e a -> (get_flag_var e)::a) hazard_preds [] in
    make_dependent_on pred_flags formula
  end

(* requires that the interpolant be mapped into the ssa betweren before and after *)
let try_interpolant_forward_k k currentState interpolant suffix  =
  match split_off_n_reversed k suffix with
  | Some(leftRev,right) ->
    let lastLeft = List.hd leftRev in
    let interpolant = remap_clause lastLeft.ssaIdxs interpolant in
    if is_valid_interpolant (currentState::leftRev) right interpolant then begin
      InterpolantWorks(interpolant,right)
    end else begin
      InterpolantFails
    end
  | None -> NotKLeft
    
(* propegate as far forward as we can, until failure.  
 * if we were using k > 1, and failed, try again with k = 1
 * Then return the new interpolant
 * and the new right side *)
let rec propegate_interpolant_forward_linear k currentState interpolant suffix = 
  match try_interpolant_forward_k k currentState interpolant suffix with 
  | InterpolantWorks (interpolant,suffix) ->
    propegate_interpolant_forward_linear k interpolant interpolant suffix 
  | InterpolantFails -> 
    if k <= 1 then interpolant,suffix 
    else propegate_interpolant_forward_linear 1 currentState interpolant suffix
  | NotKLeft -> 
    if k <= 1 then failwith "was not expecting not k left with k = 1";
    propegate_interpolant_forward_linear 1 currentState interpolant suffix

let propegate_interpolant_binarysearch currentState interpolant suffix =
  let rec helper k currentState interpolant suffix = 
    if k = 0 then interpolant,suffix 
    else match try_interpolant_forward_k k currentState interpolant suffix with 
    | InterpolantWorks (interpolant,suffix) ->
      helper (k/2) interpolant interpolant suffix 
    | InterpolantFails -> 
      helper (k/2) interpolant interpolant suffix 
    | NotKLeft -> failwith "there really should be k left now"
  in
  (* try to go forward one,  If we can't then don't bother to do a binary search *)
  match try_interpolant_forward_k 2 currentState interpolant suffix with 
  | InterpolantWorks (interpolant,suffix) ->
    debug_endline "worked";
    helper (List.length suffix) currentState interpolant suffix
  | InterpolantFails  | NotKLeft -> 
    propegate_interpolant_forward_linear 1 currentState interpolant suffix

let reduce_trace_unsatcore (unreducedClauses : trace) : trace =
  match do_smt unreducedClauses GetUnsatCore with
  | Unsat (GotUnsatCore core) ->
    List.filter (fun c -> StringSet.mem (assertion_name c) core) unreducedClauses 
  | _-> failwith "unable to get core"
    
(* all this does is find the precondition for each statement.  No reductions *)
let make_cheap_annotated_trace (clauses : trace) : annotatedTrace = 
  let partition =  make_all_interpolants clauses in
  match do_smt clauses (GetInterpolation partition) with
  | Unsat (GotInterpolant inters) -> 
    (* the interpolant list will be missing the program precondition
     * so we start with an extra interpolant "true" *)
    let zipped = List.combine (SMTTrue::inters) clauses in
    zipped
  | _ -> failwith "make_cheap_annotated_trace failed"

let reduce_trace_noninductive (input : annotatedTrace) : annotatedTrace =
  let rec aux at accum = 
    match at with
    | (i1,s1)::(i2,s2)::rest -> 
      let _ , rhsClauses = List.split rest in
      let remapped = remap_formula s1.ssaIdxs i1 in
      let interpolant = make_clause remapped s1.ssaIdxs [] Interpolant noTags in
      let c1 =  make_clause i1 emptySSAMap  [] Interpolant noTags in
      if is_valid_interpolant [c1;s1] (s2::rhsClauses) interpolant then
	aux ((remapped,s2)::rest) accum
      else 
	aux ((i2,s2)::rest) ((i1,s1)::accum)
    | [x] -> x::accum
    | _ -> failwith "here"
  in
  List.rev (aux input [])

let propegate_forward_window (input : annotatedTrace) : annotatedTrace =
  let rec aux at accum = 
    match at with
    | (i1,s1)::(i2,s2)::(i3,s3)::rest -> 
      let remapped = remap_formula s1.ssaIdxs i1 in
      let interpolant = make_clause remapped s1.ssaIdxs [] Interpolant noTags in
      let c1 = make_clause i1 emptySSAMap   [] Interpolant noTags in
      let c3 =  make_clause i3 emptySSAMap   [] Interpolant noTags in
      if is_valid_interpolant [c1;s1][s2;c3] interpolant then
	aux ((remapped,s2)::(i3,s3)::rest) accum
      else 
	aux ((i2,s2)::(i3,s3)::rest) ((i1,s1)::accum)
    | _ -> accum
  in
  List.rev (aux input [])
    
(* reduced is the prefix of the trace *)
(* We will work as follows:
 * assume that the reducedPrefix is maximally reduced
 * At the end of this prefix, we are in the state currentState
 * We need the next assignment, otherwise we would have been able 
 * to map the interpolant even further forward
 * so take : [currentState; x ; prefix] and find an interpolant between
 * x and prefix.
 * map that as far as possible
 * repeat
 * keep the reduced prefix in reverse order to prevent unneccessary list conjunctions
 *)
let reduce_trace_expensive propAlgorithm trace = 
  let rec reduce_trace_imp reducedPrefixRev currentState unreducedSuffix =
    match unreducedSuffix with
    | [] -> reducedPrefixRev
    | [x] -> (currentState.formula,x)::reducedPrefixRev
    | x :: unreducedSuffix ->
      (* We know we need to keep x, but can we reduce the suffix further? *)
      let before = [currentState;x] in
      let after = unreducedSuffix in
      let partition = make_interpolate_between before after in
      match do_smt (before @ after) (GetInterpolation partition)  with 
      | Unsat (GotInterpolant [interpolantTerm]) -> 
	let interpolant = 
	  make_clause interpolantTerm x.ssaIdxs emptyIfContext Interpolant noTags in
	(*find_farthest_point_interpolant_valid 
	 * we start in state interpolant, with guess 
	 * interpolant.  See if we can propegage it
	 * across the new suffix  *)
	let newCurrentState, unreducedSuffix = 
	  propAlgorithm interpolant interpolant unreducedSuffix in
	reduce_trace_imp 
	  ((currentState.formula,x)::reducedPrefixRev)
	  newCurrentState 
	  unreducedSuffix 
      | Sat -> failwith "was sat"
      | _ -> failwith "Problem getting interpolant"
  in
  List.rev (reduce_trace_imp [] (make_true_clause ()) trace)

let unsat_then_cheap trace =
  print_endline 
    ("started with " ^ string_of_int (List.length (reduced_linenums trace)) ^ " lines");
  let reduced = reduce_trace_unsatcore trace in
  print_endline 
    ("cheap left " ^ string_of_int (List.length (reduced_linenums reduced)) ^ " lines");
  make_cheap_annotated_trace reduced

let unsat_then_window trace = 
  let cheap = unsat_then_cheap trace in
  let window = propegate_forward_window cheap in
  debug_endline ("\n***** Finished with " ^ (string_of_int (List.length(reduced_linenums_at window))) ^ " loc *****\n\n");
  window

let unsat_then_noninductive trace = 
  let cheap = unsat_then_cheap trace in
  let noninductive = reduce_trace_noninductive cheap in
  debug_endline ("\n***** Finished with " 
		 ^ (string_of_int (List.length(reduced_linenums_at noninductive))) 
		 ^ " loc *****\n\n");
  noninductive

let unsat_then_expensive propAlgorithm trace = 
  debug_endline 
    ("started with " ^ string_of_int (List.length (reduced_linenums trace)) ^  " lines");
  let cheap = reduce_trace_unsatcore trace in
  debug_endline ("cheap left " ^ string_of_int(List.length(reduced_linenums cheap)) ^ " lines");
  (* Printf.printf "cheap left %d clauses\n" (List.length (cheap)); *)
  let expensive = reduce_trace_expensive propAlgorithm cheap in
  (* Printf.printf "expensive left %d lines\n" (List.length (reduced_linenums_at expensive)); *)
  (* Printf.printf "expensive left %d lines\n" (List.length (expensive)); *)
  debug_endline ("\n***** Finished with " ^ (string_of_int (List.length(reduced_linenums_at expensive))) ^ " loc *****\n\n");
  expensive
    
let get_partition_interpolant partitionP trace =
  let partitionString = match List.partition partitionP trace with
    | (a,b) -> make_interpolate_between a b in
  let result = do_smt trace (GetInterpolation partitionString) in
  match result with 
  | Unsat(GotInterpolant [theInterpolant]) -> theInterpolant
  | _ -> failwith "didn't get interpolant for partition"
    
(* we can either work on tid or groups, by choosing the idExtractor function *)
let summerize_annotated_trace (idExtractor : clause -> int) 
    (fullTrace : annotatedTrace) (groupId : int) =
  let rec aux remaining groupAccum groupExitCond summaryAccum =
    match remaining with 
    | [] -> List.rev groupAccum
    | (i,c) as hd::xs -> begin
      match c.typ with 
      | ProgramStmt(instr,Some thatTid) -> begin
	let inGroup = (groupId = idExtractor c) in
	match inGroup,groupExitCond with
	| true,None -> 
	  (* Were in desired thread, stayed in it*)
	  aux xs (hd::groupAccum) None [] 
	| true,Some cond  -> 
	  (* we not in the desired group, now entered it.  Have to build 
	   * the summary *)
	  let summary = make_clause 
	    (SMTRelation("=>",[cond;i])) 
	    c.ssaIdxs
	    emptyIfContext
	    (Summary(List.rev summaryAccum))
	    noTags 
	  in
	  aux xs (hd::(cond,summary)::groupAccum) None []
	| false, None  -> 
	  (* we just left the desired thread *)
	  aux xs groupAccum (Some i) ((instr,Some thatTid)::summaryAccum)
	| false, Some cond  -> 
	  (* we are out of the desired thread, and have been for at least one statment*)
	  aux xs groupAccum groupExitCond ((instr,Some thatTid)::summaryAccum)
      end
      | _ -> failwith "not a programstatment in summirization"
    end
  in
  aux fullTrace [] None []


let reduce_using_technique technique clauses  = 
  match technique with 
  | UNSATCORE -> unsat_then_cheap clauses
  | LINEARSEARCH -> unsat_then_expensive (propegate_interpolant_forward_linear 1) clauses 
  | BINARYSEARCH -> unsat_then_expensive (propegate_interpolant_binarysearch) clauses 
  | WINDOW -> unsat_then_window clauses
  | NONINDUCTIVE -> unsat_then_noninductive clauses
  | NOREDUCTION -> make_cheap_annotated_trace clauses

(****************************** Printing to files ******************************)

let annotated_trace_to_smtfile at filename = 
  let interpolants,trace = List.split at in
  print_smt (Some filename) trace CheckSat 
    
let reduce_to_file technique filename clauses =
  let reduced = reduce_using_technique technique clauses in
  calculate_stats_at "Reduced" reduced;
  print_annotated_trace_to_file filename reduced;
  if(!printReducedSMT) then 
    annotated_trace_to_smtfile reduced filename;
  reduced

let summarize_to_file technique reduced id = 
  let summarized = summerize_annotated_trace technique reduced id  in
  calculate_stats_at ("Slice" ^ string_of_int id) summarized;
  print_annotated_trace_to_file ("summary" ^ string_of_int id) summarized
    
let partition_to_file technique reduced id = 
  print_endline ("Partitioning. A group is " ^ string_of_int id);
  let interpolant = get_partition_interpolant 
    (fun x -> (technique x) = id) reduced in
  print_endline (string_of_formula interpolant)

(******************** Actually do the pass over the code ********************)

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
  let clauses = List.rev !revProgram in
  let clauses = if (!toposortInput) then Dsngraph.topo_sort clauses else clauses in
  (* add a true assertion at the begining of the program *)
  let clauses = make_true_clause () :: clauses in
  calculate_stats "Initial" clauses;
  if !printTraceSMT then print_smt (Some "fulltrace") clauses CheckSat;
  begin match !multithread with
  | PARTITIONTID -> 
    let reducedClauses = reduce_trace_unsatcore clauses in
    TIDSet.iter (partition_to_file extract_tid reducedClauses) !seenThreads
  | PARTITIONGROUP -> 
    let reducedClauses = reduce_trace_unsatcore clauses in
    GroupSet.iter (partition_to_file extract_group reducedClauses) !seenGroups
  | ALLGROUPS -> 
    let reduced = reduce_to_file !analysis "reduced" clauses in
    GroupSet.iter (summarize_to_file extract_group reduced) !seenGroups
  | ALLTHREADS ->
    let reduced = reduce_to_file !analysis "reduced" clauses in
    calculate_thread_stats clauses;
    TIDSet.iter (summarize_to_file extract_tid reduced) !seenThreads
  | ABSTRACTENV -> 
    TIDSet.iter 
      (fun tid  -> 
	print_string ("\n\n***Processing abstract thread: " ^ string_of_int tid);
	encodeFormulaOpts := 
	  {!encodeFormulaOpts with makeFlowSensitive = make_flowsensitive_this_tid tid};
	let reduced = reduce_to_file 
	  !analysis ("reduced" ^ string_of_int tid) clauses in
	summarize_to_file extract_tid reduced tid 
      ) 
      !seenThreads
  | NOMULTI -> 
    ignore(reduce_to_file !analysis "smtresult" clauses)
  end ;
  let clause_graph = Dsngraph.make_dependency_graph (clauses) in
  Dsngraph.make_dotty_file "myfile" clause_graph;
  let sorted = Dsngraph.topo_sort_graph clause_graph in
  (*print_clauses sorted;
    print_cprogram sorted;*)
  Printf.printf "%d\n" (count_contextswitches sorted);
  (*  List.iter (fun c -> print_endline (string_of_clause c)) (Dsngraph.topo_sort clause_graph);*)
  exit_all_solvers() 
    

let feature : featureDescr = 
  { fd_name = "dsnsmt";
    fd_enabled = Cilutil.dsnSmt;
    fd_description = "Converts linearized concrete c program to SMT";
    fd_extraopt = 
      [ ("--runsmtanalysistype", 
	 Arg.String 
	   (fun x -> match x with 
	   | "noreduction" -> analysis := NOREDUCTION
	   | "unsatcore" -> analysis := UNSATCORE
	   | "linearsearch" -> analysis := LINEARSEARCH
	   | "binarysearch" -> analysis := BINARYSEARCH
	   | "window" -> analysis := WINDOW
	   | "noninductive" -> analysis := NONINDUCTIVE
	   | x -> failwith (x ^ " is not a valid analysis type")),
	 " the analysis to use unsatcore linearsearch binarysearch");
	("--smtdebug", Arg.Unit (fun x -> debugLevel := 2), 
	 " turns on printing debug messages");
	("--smtprinttrace", Arg.Unit (fun x -> printTraceSMT := true), 
	 " prints the origional trace to smt");
	("--smtprintreduced", Arg.Unit (fun x -> printReducedSMT := true), 
	 " prints the reduced code to smt");
	("--toposortinput", Arg.Unit (fun x -> toposortInput := true), 
	 " Topologically Sorts the input before processing it");
	("--flowsensitive", Arg.Unit (fun x -> encodeFormulaOpts := 
	  {!encodeFormulaOpts with makeFlowSensitive = make_flowsensitive}), 
	 " Makes the encoding flow sensitive");
	("--hazardsensitiveraw", Arg.Unit (fun x -> addTrackedHazard Dsngraph.HAZARD_RAW),  
	  " Makes the encoding raw hazard sensitive");
	("--hazardsensitivewar", Arg.Unit (fun x -> addTrackedHazard Dsngraph.HAZARD_WAR),  
	  " Makes the encoding raw hazard sensitive");
	("--hazardsensitivewaw", Arg.Unit (fun x -> addTrackedHazard Dsngraph.HAZARD_WAW),  
	  " Makes the encoding raw hazard sensitive");
	("--smtmultithread", Arg.String 
	  (fun x -> match x with
	  | "partitionTID" -> multithread := PARTITIONTID
	  | "partitionGroup" -> multithread := PARTITIONGROUP
	  | "allgroups" -> multithread := ALLGROUPS
	  | "allthreads" -> multithread := ALLTHREADS
	  | "abstractenv" -> multithread := ABSTRACTENV
	  | "nomulti" -> multithread := NOMULTI
	  | x -> failwith (x ^ " is not a valid multithread analysis type")), 
	 " turns on multithreaded analysis");
      ];
    fd_doit = dsnsmt;
    fd_post_check = true
  } 

