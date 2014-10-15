(** See copyright notice at the end of this file *)
(* DSN todo rename lhsStr to ((preTypeStr,preTypeArgs),(postTypeStr,postTypeArgs)) *)
(* TODO print globals before main *)
(** Add printf before each function call *)

open Pretty
open Cil
open Trace
module E = Errormsg
module H = Hashtbl

let indexMap = Hashtbl.create 1000
let currentFunc = ref None

let init_ssa_map v = Hashtbl.add indexMap v.vname (v,0)
let update_ssa_map v newIdx = Hashtbl.add indexMap v.vname (v,newIdx)
let get_ssa_var v = let var,idx = Hashtbl.find indexMap v.vname in var

let rec update_rhs_exp e = match e with
  | Const _ | SizeOf _ | SizeOfStr _ | AlignOf _ -> e
  | Lval(l) -> Lval(update_rhs_lval l)
  | SizeOfE(e) -> SizeOfE(update_rhs_exp e)
  | AlignOfE(e) -> AlignOfE(update_rhs_exp e)
  | UnOp(o,e,t) -> UnOp(o,update_rhs_exp e, t)
  | BinOp(b,e1,e2,t) -> BinOp(b,update_rhs_exp e1, update_rhs_exp e2, t)
  | CastE(t,e) -> CastE(t,update_rhs_exp e)
  | AddrOf(l) -> AddrOf(update_rhs_lval l)
  | StartOf(l) -> StartOf(update_rhs_lval l)
  | _ -> raise (Failure "unexpected exp type")
and update_rhs_lval (lh,o) = 
  match lh with 
    | Var(v) -> Var (get_ssa_var v)
    | Mem _ -> raise (Failure "shouldn't be any mem after concrete transformation")
and update_rhs_offset o = 


class dsnVisitorClass = object
  inherit nopCilVisitor
    
  method vinst i = begin
    match i with
      | _ -> DoChildren
  end
  method vstmt (s : stmt) = begin
    match s.skind with
      | _ -> DoChildren
  end
end

(* assume that there is only one function at this point *)
(* otherwise things get messy *)
let dsnVisitor = new dsnVisitorClass

let dsn (f: file) : unit =  
  let doGlobal = function
    | GVarDecl (v, _) | GVar (v, _,_) ->  updateSSAMap v 0
    | GFun(fdec,loc) -> 
      if (fdec.svar.vname <> "main") then 
	raise (Failure "main should be the only function") else ();
      currentFunc := Some fdec;
      List.iter init_ssa_map fdec.slocals;
      List.iter init_ssa_map fdec.sformals;
      ignore (visitCilFunction dsnVisitor fdec)
    | _ -> ()
  in
  Stats.time "dsn" (iterGlobals f) doGlobal
  

let feature : featureDescr = 
  { fd_name = "dsnssa";
    fd_enabled = Cilutil.dsnSsa;
    fd_description = "convert a concrete trace to SSA form";
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
