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

module ClauseVertex = struct 
  type t = Dsnsmt.clause
  let compare=compare
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

module IntClauseMap = Map.Make(Int)
type intClauseMap = Dsnsmt.clause IntClauseMap.t
let emptyICM : intClauseMap = IntClauseMap.empty
let search_icm tid icm : clause option = 
  try Some(IntClauseMap.find tid icm) 
  with Not_found -> None

type intCLMap = (Dsnsmt.clause list) IntClauseMap.t
let emptyICLMap : intCLMap = IntClauseMap.empty
let search_iclmap tid icm = 
  try IntClauseMap.find tid icm
  with Not_found -> []

let get_uses clause = VarSet.diff clause.vars clause.defs

(* given that there is a hazard such that c1 => c2, determine the type *)
let determine_hazard c1 c2 v =
  assert (VarSet.exists (fun x -> x.vidx = v.vidx) c1.vars);
  assert (VarSet.exists (fun x -> x.vidx = v.vidx) c2.vars);
  let c1_write = VarSet.exists (fun x -> x.vidx = v.vidx) c1.defs in
  let c2_write = VarSet.exists (fun x -> x.vidx = v.vidx) c2.defs in
  match c1_write,c2_write with
  | true,true -> HAZARD_WAW
  | true,false -> HAZARD_RAW
  | false,true -> HAZARD_WAR
  | false,false -> failwith "RAR hazard???"

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
    (* Add the hazards *)
    VarSet.iter (fun v -> match search_icm v.vidx lastDefn with
    | Some c -> 
      let hazardType = determine_hazard c clause v in
      G.add_edge_e graph (G.E.create c hazardType clause)
    | None -> ()
    ) clause.vars;
    (* update the last defns *)
    let lastDefn = VarSet.fold 
      (fun e a -> IntClauseMap.add e.vidx clause a) clause.defs lastDefn in
    lastDefn,lastUses
  ) (emptyICM,emptyICLMap) clauses);

  let file = open_out_bin "mygraph.dot" in
  let () = Dot.output_graph file graph in
  graph

