open Graph
open Dsnutils
open Dsnsmtdefs

type hazard = HAZARD_RAR |  HAZARD_RAW | HAZARD_WAR | HAZARD_WAW | HAZARD_PO | NO_HAZARD
let string_of_hazard = function 
  | HAZARD_RAR -> "RAR"
  | HAZARD_RAW -> "RAW"
  | HAZARD_WAR -> "WAR" 
  | HAZARD_WAW -> "WAW" 
  | HAZARD_PO  -> "PO" 
  | NO_HAZARD  -> failwith "shouldn't ever see this"

module HazardM = struct 
  type t = hazard 
  let compare = compare               
  let hash = Hashtbl.hash 
  let equal = (=)
  let default = NO_HAZARD
end   

module HazardSet = Set.Make(HazardM)
module HazardEdge = HazardM

module ClauseM = struct
  type t = clause
  let compare = compare
  let equal = (=)
  let hash = Hashtbl.hash
end

(* Sort by tid first, to try to group tids as much as possible *)
module ClauseVertex = struct 
  type t = clause
  let compare a b = 
    match compare_tid_opt a b with
    | Some c -> c
    | None -> compare a.idx b.idx
  let equal = (=)
  let hash = Hashtbl.hash
end

module ClauseSet = Set.Make(ClauseVertex)

module G = Imperative.Digraph.ConcreteLabeled(ClauseVertex)(HazardEdge)
module Dot = Graph.Graphviz.Dot(struct
  include G (* use the graph module from above *)
  let edge_attributes (a, e, b) = [`Label (string_of_hazard e); `Color 4711]
  let default_edge_attributes _ = []
  let get_subgraph _ = None
  let vertex_attributes _ = [`Shape `Box]
  let vertex_name v = clause_name v
  let default_vertex_attributes _ = []
  let graph_attributes _ = []
end)

(* just import the G for now.  Could fix this later *)
(* DSN. I took the topological.stable_sort algorithm
 * and modified it slightly so that it maintains a reference to the last returned tid
 * This ensures that we will group things from the same tid together when possible 
 *)
module Sort_using_tid  =
struct

  module H = Hashtbl.Make(G.V)
  module C = Path.Check(G)

  let choose ~old (v, n) =
    let l, min = old in
    if n = min then v :: l, n
    else if n < min then [ v ], n
    else old

  module Q = struct
    module M = Map.Make(Int)
    type elt = G.V.t
    type q = G.V.t M.t ref
    let create () = ref M.empty
    let push v s = s := 
      let tid = extract_tid v in
      (* since we maintain PO, should only have at most one binding per thread *)
      assert(not (M.mem tid !s)); 
      M.add (extract_tid v) v !s
    let pop last s =
      let pop_binding s (k,v) = 
	s:= M.remove k !s;
	last := Some k;
	v
      in
      let get_min_binding s = 
	let binding = M.min_binding !s in (* could also use max_binding or choose *)
	pop_binding s binding
      in
      match !last with
      | None -> get_min_binding s      
      | Some lastTid -> 
	try let r = M.find lastTid !s in pop_binding s (lastTid,r)
	with Not_found -> get_min_binding s	 
    let is_empty s = M.is_empty !s
    let choose ~old new_ =
      let l, n = choose ~old new_ in
      List.sort G.V.compare l, n
  end

  let rec choose_independent_vertex checker = function
    | [] -> assert false
    | [ v ] -> v
    | v :: l ->
      (* choose [v] if each other vertex [v'] is in the same cycle
	 (a path from v to v') or is in a separate component
	 (no path from v' to v).
	 So, if there is a path from v' to without any path from v to v',
	 discard v. *)
      if List.for_all
	(fun v' -> C.check_path checker v v' || not (C.check_path checker v' v))
	l
      then
	v
      else
	choose_independent_vertex checker l

  (* in case of multiple cycles, choose one vertex in a cycle which
     does not depend of any other. *)
  let find_top_cycle checker vl =
    (* choose [v] if each other vertex [v'] is in the same cycle
       (a path from v to v') or is in a separate component
       (no path from v' to v).
       So, if there is a path from v' to without any path from v to v',
       discard v. *)
    let on_top_cycle v =
      List.for_all
	(fun v' ->
          G.V.equal v v' ||
            C.check_path checker v v' || not (C.check_path checker v' v))
        vl
    in
    List.filter on_top_cycle vl

  let fold f g acc =
    let last = ref None in
    let checker = C.create g in
    let degree = H.create 97 in
    let todo = Q.create () in
    let push x =
      H.remove degree x;
      Q.push x todo
    in
    let rec walk acc =
      if Q.is_empty todo then
        (* let's find any node of minimal degree *)
	let min, _ =
	  H.fold (fun v d old -> Q.choose ~old (v, d)) degree ([], max_int)
	in
	match min with
	| [] -> acc
	| _ ->
	  let vl = find_top_cycle checker min in
	  List.iter push vl;
          (* let v = choose_independent_vertex checker min in push v; *)
	  walk acc
      else
	let v = Q.pop last  todo in
	let acc = f v acc in
	G.iter_succ
	  (fun x->
            try
              let d = H.find degree x in
	      if d = 1 then push x else H.replace degree x (d-1)
            with Not_found ->
	      (* [x] already visited *)
	      ())
	  g v;
	walk acc
    in
    G.iter_vertex
      (fun v ->
	let d = G.in_degree g v in
	if d = 0 then Q.push v todo
	else H.add degree v d)
      g;
    walk acc

  let iter f g = fold (fun v () -> f v) g ()

end

module Top = Sort_using_tid

module IntClauseMap = Map.Make(Int)
type intClauseMap = clause IntClauseMap.t
let emptyICM : intClauseMap = IntClauseMap.empty
let search_icm id icm : clause option = 
  try Some(IntClauseMap.find id icm) 
  with Not_found -> None

type intCLMap = (clause list) IntClauseMap.t
let emptyICLMap : intCLMap = IntClauseMap.empty
let search_iclmap id icm : clause list= 
  try IntClauseMap.find id icm
  with Not_found -> []

let make_dotty_file filename graph = 
  let file = open_out_bin (filename ^ ".dot") in
  let () = Dot.output_graph file graph in
  close_out file

(* possibly use builder to remove the dependence on using imperative graphs here *)
let make_dependency_graph  ?(dottyFileName = None) clauses = 
  let clauses = 
    (List.filter (fun c -> match c.typ with ProgramStmt _ -> true | _ -> false) clauses)
  in
  let graph = G.create ~size:(List.length clauses) () in
  (* Add the verticies *)
  List.iter (fun x -> G.add_vertex graph x) clauses;

  (* add the Program order contraints *)
  ignore (List.fold_left (fun poMap clause -> 
    let tid = extract_tid clause in 
    begin match search_icm tid poMap with 
    | Some lastStmt -> 
      G.add_edge_e graph (G.E.create lastStmt HAZARD_PO clause)
    | None -> ()
    end;
    IntClauseMap.add tid clause poMap
  ) emptyICM clauses);

  (* Add the hazards *)
  ignore (List.fold_left (fun (lastDefn,lastUses) clause ->
    let uses = get_uses clause in
    let defs = clause.defs in

    (* Start by adding the RAW hazards *)
    SSAVarSet.iter (fun v -> match search_icm v.vidx lastDefn with
    | Some c -> 
      G.add_edge_e graph (G.E.create c HAZARD_RAW clause)
    | None -> ()
    ) (uses);

    (* Now the WAW *)
    SSAVarSet.iter (fun v -> match search_icm v.vidx lastDefn with
    | Some c -> 
      G.add_edge_e graph (G.E.create c HAZARD_WAW clause)
    | None -> ()
    ) (defs);

    (* Now the WAR *)
    SSAVarSet.iter (fun v -> List.iter
      (fun c -> G.add_edge_e graph (G.E.create c HAZARD_WAR clause))
      (search_iclmap v.vidx lastUses)
    ) defs;

    (* First add the uses.  Some of these might get overridden in the next step *)
    let lastUses = SSAVarSet.fold (fun v lastUses -> 
      let oldUses = search_iclmap v.vidx lastUses in
      let updatedUses = clause::oldUses in
      IntClauseMap.add v.vidx updatedUses lastUses
    ) uses lastUses in

    let (lastDefn,lastUses) = SSAVarSet.fold 
      (fun v (lastDefn,lastUses) -> 
	(IntClauseMap.add v.vidx clause lastDefn, 
	 IntClauseMap.remove v.vidx lastUses)
      ) defs (lastDefn,lastUses) in

    lastDefn,lastUses
  ) (emptyICM,emptyICLMap) clauses);

  (* Optionally Print out the graph *)
  (match dottyFileName with 
  | None -> ()
  | Some filename -> make_dotty_file filename graph);

  graph 
    
let topo_sort_graph graph = 
  List.rev (Top.fold (fun c lst -> c::lst)  graph [])

let topo_sort  ?(dottyFileName = None) clauses = 
  let clause_graph = make_dependency_graph ~dottyFileName:dottyFileName clauses in
  topo_sort_graph clause_graph 
    
(* Given a vertex and a set of hazards, get all the clauses that that 
 * are predecessors to the clause by some hazard relation *)
let get_hazard_preds graph hazards vertex =
  G.fold_pred_e 
    (fun edge acc -> 
      if (HazardSet.mem (G.E.label edge) hazards) 
      then ClauseSet.add (G.E.src edge) acc
      else acc
    ) graph vertex ClauseSet.empty
    
