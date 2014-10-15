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

let dsnVisitor = new dsnVisitorClass

let dsn (f: file) : unit =  
  let doGlobal = function
    | GVarDecl (v, _) -> Hashtbl.add indexMap v.vname 0
    | GFun(fdec,loc) -> currentFunc := Some fdec
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
