(** See copyright notice at the end of this file *)

(*
 * This conversion is not perfect. For example, overflow may happen.
 *)

open Cil
module E = Errormsg

class dsnVisitorClass = object
  inherit nopCilVisitor

  (* Types become signed long long. *)
  method vtype t = match t with
    | TInt(_, a) | TPtr(_, a) | TArray(_, _, a) | TNamed(_, a) ->
        ChangeTo (TInt(ILongLong, dropAttribute "restrict" a))
    | TFloat _ -> E.s (E.bug "Float not supported.")
    | _ -> DoChildren

  method vexpr e = match e with
    | BinOp(op, e1, e2, t) -> begin match op with
      | PlusPI | MinusPI ->
        let sz_ptr = (bitsSizeOf (unrollTypeDeep t)) / 8 in
        let e1' = BinOp(Mult, e1, integer sz_ptr, t) in
        ChangeTo (BinOp(op, e1', e2, t))
      | IndexPI -> E.s (E.bug "IndexPI not expected.")
      | MinusPP -> E.s (E.bug "Let's see if MinusPP is expected.")
      | _ -> DoChildren end
    | CastE(_, e1) -> ChangeTo e1
    | _ -> DoChildren

   (* Restore the type of 'main' after everything became signed long long. *)
   method vfunc fdec =
    if fdec.svar.vname <> "main" then E.s (E.bug "Expecting 'main' only.");
    let fix_main f =
      f.svar <- makeGlobalVar "main" (TFun(intType, Some [], false,[]));
      f.sformals <- [];
      ignore (makeFormalVar f "argc" intType);
      ignore (makeFormalVar f "argv" (TPtr(charPtrType, [])));
      f in
    ChangeDoChildrenPost (fdec, fix_main)
end

let dsnVisitor = new dsnVisitorClass

let dsnsll (f: file) : unit =
  (* Drop typedefs, structs and unions (forward decl or def), and enums. *)
  let pred = function
    | GType _ | GVarDecl _ | GCompTag _ | GCompTagDecl _
    | GEnumTag _ | GEnumTagDecl _ -> false
    | _ -> true in
  f.globals <- List.filter pred f.globals;
  let doGlobal g = ignore (visitCilGlobal dsnVisitor g) in
  Stats.time "dsn" (iterGlobals f) doGlobal


let feature : featureDescr =
  { fd_name = "dsnsll";
    fd_enabled = Cilutil.dsnSll;
    fd_description = "convert every type to signed long long";
    fd_extraopt = [];
    fd_doit = dsnsll;
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
