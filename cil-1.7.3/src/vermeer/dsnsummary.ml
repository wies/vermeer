open Dsnsmt
open Graph
open Dsnutils
open Cil
open Dsnsmtdefs
open Dsnctosmt

(****************************** Globals and types ******************************)
type analysis = 
  UNSATCORE | LINEARSEARCH | BINARYSEARCH | WINDOW | NONINDUCTIVE | NOREDUCTION
let analysis = ref UNSATCORE (*default *)
let summarizeThread = ref false
type multithreadAnalysis = 
  ALLGROUPS | ALLTHREADS | ABSTRACTENV | NOMULTI | PARTITIONTID | PARTITIONGROUP

type summaryOpts =  {
  mutable multithread : multithreadAnalysis;
  mutable printTraceSMT : bool;
  mutable printReducedSMT : bool;
  mutable toposortInput : bool ;
  mutable toposortOutput : bool ;
  mutable trackedHazards : HazardSet.t;
  mutable calcStats : bool;
  mutable intrathreadHazards : bool;
  mutable axiomMaker : axiomFn;
}

let opts = {
  multithread = NOMULTI;
  printTraceSMT = false;
  printReducedSMT = false;
  toposortInput = false;
  toposortOutput = false;
  trackedHazards = HazardSet.empty;
  calcStats = false;
  intrathreadHazards = true;
  axiomMaker = makeEmptyAxioms;
}

let addTrackedHazard hazard = opts.trackedHazards <- HazardSet.add hazard opts.trackedHazards

(****************************** encoding rules ******************************)

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
  match get_unsat_core unreducedClauses with
  | UnsatCore core ->
    List.filter (fun c -> StringSet.mem (clause_name c) core) unreducedClauses 
  | _-> failwith "unable to get core"
    
(* all this does is find the precondition for each statement.  No reductions *)
let make_cheap_annotated_trace (clauses : trace) : annotatedTrace = 
  let partition =  make_all_interpolants clauses in
  match get_interpolant clauses partition with
  | Interpolant inters -> 
    (* the interpolant list will be missing the program precondition
     * so we start with an extra interpolant "true" *)
    let zipped = List.combine (SB.mk_true::inters) clauses in
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
      match get_interpolant (before @ after) partition  with 
      | Interpolant [interpolantTerm] -> 
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
  let result = get_interpolant trace partitionString in
  match result with 
  | Interpolant [theInterpolant] -> theInterpolant
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
	    (SB.mk_impl cond i) 
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
      | Axiom s -> aux xs (hd::groupAccum) None [] (* TODO make sure this works *)
      | _ -> failwith "not a program statment in summarization"
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

(* let annotated_trace_to_smtfile at filename =  *)
(*   let interpolants,trace = List.split at in *)
(*   print_smt (Some filename) trace CheckSat  *)
    
let reduce_to_file technique filename clauses =
  let reduced = reduce_using_technique technique clauses in
  if opts.calcStats then calculate_stats_at "Reduced" reduced;
  print_annotated_trace_to_file filename reduced;
  reduced

let summarize_to_file ?(filenameOpt = None) technique reduced id = 
  let filename = match filenameOpt with
    | Some filename -> filename
    | None -> ("threadSlice" ^ string_of_int id) in
  let summarized = summerize_annotated_trace technique reduced id  in
  let summarized = if opts.toposortOutput 
    then failwith "not quite supporting this yet"
    else summarized in
  if opts.calcStats then calculate_stats_at ("slice" ^ string_of_int id) summarized;
  print_annotated_trace_to_file filename summarized
    
let partition_to_file technique reduced id = 
  print_endline ("Partitioning. A group is " ^ string_of_int id);
  let interpolant = get_partition_interpolant 
    (fun x -> (technique x) = id) reduced in
  print_endline (string_of_formula interpolant)

(******************** Actually do the pass over the code ********************)

let dsnsmt (f: file) : unit =
  (* check that we are only sorting if we are using multithreaded analysis *)
  let _ = if (opts.multithread = NOMULTI) then begin
    assert(not opts.toposortInput);
    assert(HazardSet.is_empty opts.trackedHazards)
  end in
  let make_graph = opts.toposortInput || not (HazardSet.is_empty opts.trackedHazards) in
  (* DSN - the parse sets a global var.  Not ideal *)
  (Dsnctosmt.parse_file f make_graph);
  (* Now toposort it, if reqested *)
  if (opts.toposortInput) then topoSortCurrent();

  (* add the hazard tracking if needed *)
  if not (HazardSet.is_empty opts.trackedHazards) then begin
    encode_hazards 
      (getCurrentGraph()) 
      opts.trackedHazards 
      opts.intrathreadHazards
  end;

  (* add a true assertion at the begining of the program *)
  let axioms = opts.axiomMaker() in
  print_endline (string_of_int (List.length axioms));
  let clauses = make_true_clause() :: (axioms @ getCurrentClauses()) in
  if opts.calcStats then calculate_stats "Initial" clauses;
  begin match opts.multithread with
  | PARTITIONTID -> 
    let reducedClauses = reduce_trace_unsatcore clauses in
    TIDSet.iter (partition_to_file extract_tid reducedClauses) 
      (getCurrentSeenThreads())
  | PARTITIONGROUP -> 
    let reducedClauses = reduce_trace_unsatcore clauses in
    GroupSet.iter (partition_to_file extract_group reducedClauses) 
      (getCurrentSeenGroups())
  | ALLGROUPS -> 
    let reduced = reduce_to_file !analysis "reduced" clauses in
    GroupSet.iter (summarize_to_file extract_group reduced) 
      (getCurrentSeenGroups())
  | ALLTHREADS ->
    calculate_thread_stats (getCurrentSeenThreads()) clauses;
    let reduced = reduce_to_file !analysis "reduced" clauses in
    TIDSet.iter (summarize_to_file extract_tid reduced) (getCurrentSeenThreads())
  | ABSTRACTENV -> 
    calculate_thread_stats (getCurrentSeenThreads()) clauses;
    TIDSet.iter 
      (fun tid  -> 
	print_endline ("\n\n***Processing abstract thread: " ^ string_of_int tid);
	encode_flowsensitive_this_tid tid;
	let reduced = reduce_to_file 
	  !analysis ("reduced" ^ string_of_int tid) clauses in
	TIDSet.iter (fun sliceTid -> 
	  summarize_to_file extract_tid 
	    ~filenameOpt:(Some("slice" ^ string_of_int tid 
			       ^"_" ^ string_of_int sliceTid))
	    reduced sliceTid) (getCurrentSeenThreads())
      )(getCurrentSeenThreads())
  | NOMULTI -> 
    ignore(reduce_to_file !analysis "smtresult" clauses)
  end ;
  exit_all_solvers() 
      
let safe_shutdown f = 
  Printexc.record_backtrace true;
  try dsnsmt f 
  with e -> (
    exit_all_solvers();
    (match e with
    | Failure s -> print_endline s
    | _ -> Printf.printf "%s\n" (Printexc.to_string e));
    exit 1
  )

  let feature : featureDescr = 
    { fd_name = "dsnsmt";
      fd_enabled = Cilutil.dsnSmt;
      fd_description = "Converts linearized concrete c program to SMT";
      fd_extraopt = 
	[ ("--runsmtanalysistype", 
	   Arg.String 
	     (function 
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
	  ("--smtcalcstats", Arg.Unit (fun x -> opts.calcStats <- true), 
	   " turns on statistics");
	  ("--smtprinttrace", Arg.Unit (fun x -> opts.printTraceSMT <- true), 
	   " prints the origional trace to smt");
	  ("--smtprintreduced", Arg.Unit (fun x -> opts.printReducedSMT <- true), 
	   " prints the reduced code to smt");
	  ("--toposortinput", Arg.Unit (fun x -> opts.toposortInput <- true), 
	   " Topologically Sorts the input before processing it");
	  ("--toposortoutput", Arg.Unit (fun x -> opts.toposortInput <- true), 
	   " Topologically Sorts the reduced trace before outputting it");
	  ("--flowsensitive", Arg.Unit (fun x -> encode_flowsensitive ()), 
	   " Makes the encoding flow sensitive");
	  ("--nointrathreadhazard", 
	   Arg.Unit (fun x -> opts.intrathreadHazards <- false),  
	   " Only considers data-hazards that are between threads ");
	  ("--hazardsensitiveall", Arg.Unit (fun x -> 
	    addTrackedHazard Dsngraph.HAZARD_RAW;
	    addTrackedHazard Dsngraph.HAZARD_WAR;
	    addTrackedHazard Dsngraph.HAZARD_WAW),  
	   " Makes the encoding RAW, WAR, and WAW hazard sensitive");
	  ("--hazardsensitiveraw", Arg.Unit (fun x -> addTrackedHazard Dsngraph.HAZARD_RAW),  
	   " Makes the encoding raw hazard sensitive");
	  ("--hazardsensitivewar", Arg.Unit (fun x -> addTrackedHazard Dsngraph.HAZARD_WAR),  
	   " Makes the encoding raw hazard sensitive");
	  ("--hazardsensitivewaw", Arg.Unit (fun x -> addTrackedHazard Dsngraph.HAZARD_WAW),  
	   " Makes the encoding raw hazard sensitive");
	  ("--hbsensitive", Arg.String (fun x ->
	    encode_hb();
	    match x with
	      | "totalorder" -> opts.axiomMaker <- makeTotalOrderAxioms
	      | "partialorder" -> opts.axiomMaker <- makeHazardAxioms
	      | x -> failwith (x ^ " is not a valid argument for --hbsensitive")),
	   " Makes the encoding happens-before sensitive");
	  ("--smtbeautify", Arg.Unit (fun x -> Dsnsmt.opts.beautifyFormulas <- true),
	   "beautifies formulas before making them into clauses");
	  ("--smtmultithread", Arg.String 
	    (fun x -> match x with
	    | "partitionTID" -> opts.multithread <- PARTITIONTID
	    | "partitionGroup" -> opts.multithread <- PARTITIONGROUP
	    | "allgroups" -> opts.multithread <- ALLGROUPS
	    | "allthreads" -> opts.multithread <- ALLTHREADS
	    | "abstractenv" -> opts.multithread <- ABSTRACTENV
	    | "nomulti" -> opts.multithread <- NOMULTI
	    | x -> failwith (x ^ " is not a valid multithread analysis type")), 
	   " turns on multithreaded analysis");
	];
      fd_doit = safe_shutdown;
      fd_post_check = true
    } 

