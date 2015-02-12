open Graph
open Dsnutils
open Dsnsmt

type hazard = HAZARD_RAR |  HAZARD_RAW | HAZARD_WAR | HAZARD_WAW | HAZARD_PO | NO_HAZARD
let string_of_hazard = function 
  | HAZARD_RAR -> "RAR"
  | HAZARD_RAW -> "RAW"
  | HAZARD_WAR -> "WAR" 
  | HAZARD_WAW -> "WAW" 
  | HAZARD_PO  -> "PO" 
  | NO_HAZARD  -> failwith "shouldn't ever see this"

module HazardEdge = struct 
  type t = hazard 
  let compare = compare               
  let hash = Hashtbl.hash 
  let equal = (=)
  let default = NO_HAZARD
end   

(* Sort by tid first, to try to group tids as much as possible *)
module ClauseVertex = struct 
  type t = Dsnsmt.clause
  let compare a b = 
    match Dsnsmt.compare_tid_opt a b with
    | Some c -> c
    | None -> compare a.idx b.idx
  let equal = (=)
  let hash = Hashtbl.hash
end

module G = Imperative.Digraph.ConcreteLabeled(ClauseVertex)(HazardEdge)
module Dot = Graph.Graphviz.Dot(struct
   include G (* use the graph module from above *)
   let edge_attributes (a, e, b) = [`Label (string_of_hazard e); `Color 4711]
   let default_edge_attributes _ = []
   let get_subgraph _ = None
   let vertex_attributes _ = [`Shape `Box]
   let vertex_name v = assertion_name v
   let default_vertex_attributes _ = []
  let graph_attributes _ = []
end)
module Top = Graph.Topological.Make_stable(G)

module IntClauseMap = Map.Make(Int)
type intClauseMap = Dsnsmt.clause IntClauseMap.t
let emptyICM : intClauseMap = IntClauseMap.empty
let search_icm id icm : clause option = 
  try Some(IntClauseMap.find id icm) 
  with Not_found -> None

type intCLMap = (Dsnsmt.clause list) IntClauseMap.t
let emptyICLMap : intCLMap = IntClauseMap.empty
let search_iclmap id icm : clause list= 
  try IntClauseMap.find id icm
  with Not_found -> []


(* possibly use builder to remove the dependence on using imperative graphs here *)
let make_dependency_graph clauses = 
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
    VarSet.iter (fun v -> match search_icm v.vidx lastDefn with
    | Some c -> 
      G.add_edge_e graph (G.E.create c HAZARD_RAW clause)
    | None -> ()
    ) (uses);

    (* Now the WAW *)
    VarSet.iter (fun v -> match search_icm v.vidx lastDefn with
    | Some c -> 
      G.add_edge_e graph (G.E.create c HAZARD_WAW clause)
    | None -> ()
    ) (defs);

    (* Now the WAR *)
    VarSet.iter (fun v -> List.iter
      (fun c -> G.add_edge_e graph (G.E.create c HAZARD_WAR clause))
      (search_iclmap v.vidx lastUses)
    ) defs;

    (* First add the uses.  Some of these might get overridden in the next step *)
    let lastUses = VarSet.fold (fun v lastUses -> 
      let oldUses = search_iclmap v.vidx lastUses in
      let updatedUses = clause::oldUses in
      IntClauseMap.add v.vidx updatedUses lastUses
    ) uses lastUses in

    let (lastDefn,lastUses) = VarSet.fold 
      (fun v (lastDefn,lastUses) -> 
	(IntClauseMap.add v.vidx clause lastDefn, 
	 IntClauseMap.remove v.vidx lastUses)
      ) defs (lastDefn,lastUses) in

    lastDefn,lastUses
  ) (emptyICM,emptyICLMap) clauses);
  graph 
    
let make_dotty_file filename graph = 
  let file = open_out_bin (filename ^ ".dot") in
  let () = Dot.output_graph file graph in
  close_out file

let topo_sort graph = 
  List.rev (Top.fold (fun c lst -> c::lst)  graph [])

