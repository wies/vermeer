(** See copyright notice at the end of this file *)

open Pretty
open Cil
open Trace
open Dsnutils
module E = Errormsg
module H = Hashtbl

module IntOrder = struct
  type t = int
  let compare = Pervasives.compare
end

module IntSet = Set.Make (IntOrder)

let used = ref IntSet.empty
let removed = ref false

let count_body_lines fdec =
  let rec f_stmt acc = function
    | [] -> acc
    | s::ss ->
      let acc = (get_stmtLoc s.skind).line::acc in
      let acc = match s.skind with
        | If(_, t, e, _) -> f_stmt (f_stmt acc t.bstmts) e.bstmts
        (*| Block b -> f_stmt acc b.bstmts*)
        | Instr is -> f_instr acc is
        | Return _ -> acc
        | _ -> E.s (E.bug "Not exprected: %a" d_stmt s) in
      f_stmt acc ss
  and f_instr acc is =
    List.fold_left (fun acc i -> (get_instrLoc i).line::acc) acc is in

  let lst_lines = f_stmt [] fdec.sbody.bstmts in
  let lst_lines = List.filter (fun i -> i != -1) lst_lines in
  List.length (compress lst_lines)

let rec mark_used_lv = function
  | (Var vi, _) -> used := IntSet.add vi.vid !used
  | (Mem e, _) -> mark_used e
and mark_used exp =
  match exp with
  | AddrOf lv | Lval lv -> mark_used_lv lv
  | CastE(_, e) | UnOp(_, e, _) -> mark_used e
  | Const(CEnum(e, _, _)) -> mark_used e
  | Const _ -> ()
  | BinOp(_, e1, e2, _) -> mark_used e1; mark_used e2

  | StartOf _ | AlignOf _ | AlignOfE _ | SizeOf _ | SizeOfE _ | SizeOfStr _
  | Question _ | AddrOfLabel _ -> E.s (E.bug "Exp %a Not expected." d_exp exp)

(* Mark variables used if they have ever appeared on the RHS of an asgn,
   or in a condition of an if-stmt. *)
class dsnMarkVisitorClass = object
  inherit nopCilVisitor

  (* Pin the last asgn in main() (if the last intr is not a call to 'assert'
     by marking its LHS used to preserve it. *)
  (* The only function being visited is main(). *)
  method vfunc fdec =
    (* Given a list of instrs in an reverse order, search for the last asgn
       and mark its LHS. If an asgn was found, return true. *)
    let rec mark_last_asgn_is = function
      | [] -> false
      | ((Set(lv, _, _)) as i)::_ ->
        E.log "[dsnrmtmps] Marking \"%a\" in\n%a\n\n" d_lval lv d_instr i;
        mark_used_lv lv; true
        (* The only call possible is 'assert', whose exp will also be marked
           in 'vinst', so let's ignore it and stop here. *)
      | (Call _)::is -> true
      | (Asm _)::_ -> E.s (E.bug "Asm not expected.") in
    (* Same functionality, but with a stmt list. *)
    let rec mark_last_asgn = function
      | [] -> E.s (E.bug "main() with no assignment?")
      | s::stmts -> begin match s.skind with
        | Return _ -> mark_last_asgn stmts
        | Instr is ->
          let rev_is = List.rev is in
          if not (mark_last_asgn_is rev_is) then mark_last_asgn stmts
        | If _ -> E.s (E.bug "I don't think it can reach an if-stmt.")
        | Block _ -> E.s (E.bug "I don't think it can reach a block.")
        | Goto _ | ComputedGoto _ | Break _ | Continue _ | Switch _
        | Loop _ | TryFinally _ | TryExcept _ ->
          E.s (E.bug "Unexpected stmtkind.")
        end in
    let rev_stmts = List.rev fdec.sbody.bstmts in
    mark_last_asgn rev_stmts;
    DoChildren

  (* Mark variables appearing on the RHS of an asgn used. *)
  method vinst = function
    | Set(_, e, _) -> mark_used e; DoChildren
    | Call(_, e, args, _) as fnCall ->
      assert_is_assert fnCall;
      List.iter mark_used args;
      DoChildren
    | _ -> E.s (E.bug "was not expecting call or asm at this point")

  (* Mark variables appearing in an if-stmt condition. *)
  method vstmt s = match s.skind with
    | If(e, _, _, _) -> mark_used e; DoChildren
    | _ -> DoChildren
end

(* With the used variable information, remove irrelevant asgns. *)
class dsnAsgnRmVisitorClass = object
  inherit nopCilVisitor

  method vinst = function
    | Set((Var vi, _), _, _) ->
      if IntSet.mem vi.vid !used then DoChildren
                                 else (removed := true; ChangeTo [])
    | Set _ -> E.s (E.bug "LHS lval should always be a variable.")
    | Call(_, _, _, _) -> DoChildren
    | _ -> E.s (E.bug "was not expecting call or asm at this point")
end

let is_used_vi vi = IntSet.mem vi.vid !used

let is_used = function
  | GVarDecl(vi, _) | GVar(vi, _, _) -> is_used_vi vi
  | _ -> true

(* Remove local variables of main. Remove empty if-stmts too. *)
let rm_locals_empty_ifs = function
  | GFun(fdec, _) ->
    (* First, local variables. *)
    fdec.slocals <- List.filter is_used_vi fdec.slocals;

    (* Next, empty if-stmts. *)
    let old_sz = List.length fdec.sbody.bstmts in
    let rec empty_stmts = function
      | [] -> true
      | s::stmts -> match s.skind with
        | Instr is -> (is = []) && (empty_stmts stmts)
        | Block b | If(_, b, _, _) ->
          (empty_stmts b.bstmts) && (empty_stmts stmts)
        | _ -> E.s (E.bug "Not expected.") in
    let non_empty_if s = match s.skind with
      | If(_, then_b, _, _) when empty_stmts then_b.bstmts -> false
      | _ -> true in
    fdec.sbody.bstmts <- List.filter non_empty_if fdec.sbody.bstmts;

    if old_sz <> List.length fdec.sbody.bstmts then begin
      removed := true;
      fdec.sbody.bstmts <- compactStmts fdec.sbody.bstmts
    end

  | _ -> ()

let main_body_lines globals =
  let f a g = match g with GFun(fdec, _) -> count_body_lines fdec | _ -> a in
  List.fold_left f 0 globals

let dsn (f: file) : unit =
  let n1 = main_body_lines f.globals in

  let dsnMarkVisitor = new dsnMarkVisitorClass in
  let dsnAsgnRmVisitor = new dsnAsgnRmVisitorClass in
  let mark g = ignore (visitCilGlobal dsnMarkVisitor g) in
  let rm_asgns g = ignore (visitCilGlobal dsnAsgnRmVisitor g) in

  let rec one_cycle f i =
    E.log "[dsnrmtmps] Cycle #%d:\n" i;
    Stats.time "dsn" iterGlobals f mark;
    Stats.time "dsn" iterGlobals f rm_asgns;
    Stats.time "dsn" iterGlobals f rm_locals_empty_ifs;
    f.globals <- List.filter is_used f.globals;
    if !removed then begin (* Repeating until a fixpoint. *)
      removed := false;
      used := IntSet.empty;
      one_cycle f (i+1)
    end in
  one_cycle f 1;

  let n2 = main_body_lines f.globals in
(*
  print_endline ("No. lines in main (fdec.sbody.stmts): "^(string_of_int n1));
  print_endline ("After reduction: "^(string_of_int n2))
*)
  print_endline ("\n***** Started with " ^ (string_of_int n1) ^ " loc *****\n\n")

let feature : featureDescr =
  { fd_name = "dsnrmtmps";
    fd_enabled = Cilutil.dsnRmTmps;
    fd_description = "Remove unused variables.";
    fd_extraopt = [];
    fd_doit = dsn;
    fd_post_check = true;
  }

(*
   *
   * Copyright (c) 2001-2002,
   *  George C. Necula    <necula@cs.berkeley.edu>
   *  Scott McPeak        <smcpeak@cs.berkeley.edu>
   *  Wes Weimer          <weimer@cs.berkeley.edu>
   * All rights reserved.
   *
   * Redistribution and use in source and binary forms, with or without
   * modification, are permitted provided that the following conditions are
   * met:
   *
   * 1. Redistributions of source code must retain the above copyright
   * notice, this list of conditions and the following disclaimer.
   *
   * 2. Redistributions in binary form must reproduce the above copyright
   * notice, this list of conditions and the following disclaimer in the
   * documentation and/or other materials provided with the distribution.
   *
   * 3. The names of the contributors may not be used to endorse or promote
   * products derived from this software without specific prior written
   * permission.
   *
   * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
   * IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
   * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
   * PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER
   * OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
   * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
   * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
   * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
   * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
   * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
   * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
   *
*)
