(**************************************************************************)
(*                                                                        *)
(*  Ocamlgraph: a generic graph library for OCaml                         *)
(*  Copyright (C) 2004-2007                                               *)
(*  Sylvain Conchon, Jean-Christophe Filliatre and Julien Signoles        *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2, with the special exception on linking              *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

(* Ocamlgraph demo program: solving the Sudoku puzzle using graph coloring *)

open Graph
open Dsnutils

type hazard = HAZARD_RAR |  HAZARD_RAW | HAZARD_WAR | HAZARD_WAW

(* We use undirected graphs with nodes containing a pair of integers
   (the cell coordinates in 0..8 x 0..8).
   The integer marks of the nodes will store the colors. *)
module G = Imperative.Graph.AbstractLabeled(struct type t = int * int end)(Int)

let make_dependency_graph x = x

(*
Local Variables: 
compile-command: "make -C .. bin/sudoku.opt"
End: 
*)
