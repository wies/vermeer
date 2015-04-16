(***************************************)
open SmtLibSyntax
open Smtlib_util
open Unix
module Util = Smtlib_util

let fail session msg = failwith "blah"

type solver_kind =
  | Process of string * string list
  | Logger

type solver_info = 
    { version: int;
      subversion: int;
      has_set_theory: bool;
      smt_options: (string * bool) list;
      kind: solver_kind; 
    }

type solver = 
    { name : string;
      info : solver_info
    }


type solver_state = 
    { out_chan: out_channel;
      in_chan: in_channel option;
      pid: int;     
    }

type session = { log_file_name: string;
                 sat_means: string;
		 mutable assert_count: int;
		 mutable sat_checked: (solver_state option * response) option;
		 stack_height: int;
                 (* signature: (arity list SymbolMap.t) option; *)
                 (* named_clauses: (string, form) Hashtbl.t option; *)
                 solvers: (solver * solver_state) list
	       }

let read_from_chan session chan =
  let lexbuf = Lexing.from_channel chan in
  SmtLibLexer.set_file_name lexbuf session.log_file_name; 
  SmtLibParser.output SmtLibLexer.token lexbuf

let read session = 
  let in_descrs = 
    Util.flat_map 
      (fun (_, state) -> 
        flush state.out_chan;
        Opt.to_list (Opt.map descr_of_in_channel state.in_chan))
      session.solvers 
  in
  (* if in_descrs = [] then  *)
  (*   (if !Config.verify then None, Unknown else None, Unsat) *)
  (* else *)
  let ready, _, _ = Unix.select in_descrs [] [] (-1.) in
  let in_descr = List.hd ready in
  let in_chan = in_channel_of_descr in_descr in
  let result = read_from_chan session in_chan in
  let state = 
    snd (List.find
           (fun (_, state) -> 
             Opt.get_or_else false 
               (Opt.map (fun c -> descr_of_in_channel c = in_descr) state.in_chan))
           session.solvers)
  in
  Some state, result

let write session cmd =
  List.iter 
    (fun (_, state) -> output_string state.out_chan cmd)
    session.solvers

let num_of_sat_queries = ref 0

let writeln session cmd = 
  write session (cmd ^ "\n")  

let is_sat session = 
  incr num_of_sat_queries;
  writeln session "(check-sat)";
  let response = read session in
  session.sat_checked <- Some response;
  match snd response with
  | Sat -> Some true
  | Unsat -> Some false
  | Unknown -> None
  | Error e -> fail session e
  | _ -> fail session "unexpected response from prover"
