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
let reverseMap = Hashtbl.create 1000
let mainFunc = ref None
let initInstrs = ref []
let varIdCtr = ref 0

let d_string (fmt : ('a,unit,doc,string) format4) : 'a = 
  let f (d: doc) : string = Pretty.sprint 800 d in
  Pretty.gprintf f fmt 

let find_safe h k = try Some (Hashtbl.find h k) with Not_found -> None
let find_var k = find_safe indexMap k.vname  
let getFd () = match !mainFunc with
  | Some fd -> fd
  | None -> failwith "no fundec at this point"

let new_ssa_var v = 
  let varId,idx = 
    match find_var v with
      | Some (_,id,idx) -> id,idx + 1
      | None -> 
	incr varIdCtr;
	Hashtbl.replace reverseMap !varIdCtr v.vname;
	!varIdCtr,0
  in
  let fd = getFd () in
  let newvarName = "x_" ^ string_of_int varId ^ "_" ^ (string_of_int idx) in
  let newVar = makeLocalVar fd newvarName v.vtype in
  Hashtbl.replace indexMap v.vname (newVar,varId,idx);
  newVar

let get_ssa_var v = 
  match find_var v with
    | Some(newVar,varId,idx) -> newVar
    | None -> new_ssa_var v

let rec update_rhs_exp e = 
  match constFold true e with
    | Const _ | SizeOf _ | SizeOfStr _ | AlignOf _ as e -> e
    | Lval(l) -> Lval(update_rhs_lval l)
    | SizeOfE(e) -> SizeOfE(update_rhs_exp e)
    | AlignOfE(e) -> AlignOfE(update_rhs_exp e)
    | UnOp(o,e,t) -> UnOp(o,update_rhs_exp e, t)
    | BinOp(b,e1,e2,t) -> BinOp(b,update_rhs_exp e1, update_rhs_exp e2, t)
    | CastE(t,e) -> CastE(t,update_rhs_exp e)
    | AddrOf(l) -> AddrOf(update_rhs_lval l)
    | StartOf(l) -> StartOf(update_rhs_lval l)
    | _ -> failwith "unexpected exp type"
and update_rhs_lval  = function  
  | Var v, NoOffset -> Var (get_ssa_var v), NoOffset
  | _ -> failwith "shouldn't be any mem after concrete transformation"

let rec update_lhs_lval = function 
  | Var v, NoOffset -> Var (new_ssa_var v), NoOffset
  | _ -> failwith "LHS shouldn't be any mem or offsets after concrete transformation"

class dsnVisitorClass = object
  inherit nopCilVisitor
    
  method vfunc f = 
    let doPost x = 
      x.sbody.bstmts <- compactStmts(mkStmt (Instr(!initInstrs))::x.sbody.bstmts);
      (*Rmciltmps.eliminate_temps x*)
      x
    in
    ChangeDoChildrenPost (f,doPost)

  method vinst i = begin
    match i with
      | Set(lhs,rhs,loc) -> 
	(* need to do right before left because the map updates after left *)  
	let updated_rhs = update_rhs_exp rhs in
	let updated_lhs = update_lhs_lval lhs in
	ChangeTo [Set(updated_lhs,updated_rhs,loc)]
      | Call(lo,e,al,l) ->
	let fname = d_string "%a" d_exp e in
	if fname <> "assert" then 
	  failwith "shouldn't have non-assert calls in a concrete trace";
	ChangeTo [Call(lo,e,List.map update_rhs_exp al,l)]
      | _ -> failwith "was not expecting call or asm at this point"
  end
  method vstmt (s : stmt) = begin
    let replace_skind sk : stmt = 
      (* we don't need to replace the CFG stuff *)
      let nstmt = mkStmt sk in
      nstmt.labels <- s.labels;
      nstmt in
    match s.skind with
      | Return (Some e, loc) -> (*the return at the end of main *)
	ChangeTo (replace_skind (Return (Some (update_rhs_exp e),loc)))
      | If (c,t,e,l) -> 
	let newCond = update_rhs_exp c in
	let updatedStmt = replace_skind (If(newCond,t,e,l)) in
	ChangeDoChildrenPost (updatedStmt, (fun x -> x))
      | Return _ | Instr _ | Block _ -> DoChildren
      | Goto _ | Break _ | Continue _ | TryFinally _ | TryExcept _ 
      | Switch _ | Loop _ | ComputedGoto _
	-> failwith "did not expect to see these in the trace at this point"
  end
end

class updateToInt = object
  inherit nopCilVisitor

  method vexpr = function
    | _ -> DoChildren    
      
end


(* assume that there is only one function at this point *)
(* otherwise things get messy *)
let dsnVisitor = new dsnVisitorClass

let dsn (f: file) : unit =  
  let findMain = function
    | GFun(fdec,loc) -> 
      if (fdec.svar.vname <> "main") then failwith "main should be the only function";
      fdec.slocals <- []; (* Clear all local variables. *)
      mainFunc := Some fdec;
    | _ -> ()
  in 
  iterGlobals f findMain;
  let globalVarToLocal a g = match g with
    | GVar (v,init,loc) -> 
      let rhs = match init.init with
	| None -> zero
	| Some(SingleInit(e)) -> update_rhs_exp e
	| Some(CompoundInit _) -> failwith "not handeling compound init"
      in
      let lhs = Var (new_ssa_var v), NoOffset in
      Set(lhs,rhs,loc)::a    
    | _ -> a
  in
  initInstrs := List.rev (foldGlobals f globalVarToLocal []);
  let _ = match !mainFunc with
    | Some (main) ->  ignore (visitCilFunction dsnVisitor main)
    | None -> failwith "could not find main!"
  in
  f.globals <- List.filter 
    (function
      | GFun _ | GText _ -> true 
      | _ -> false
    ) f.globals;
  let assocList = Hashtbl.fold (fun k v a -> (k,v) :: a) reverseMap [] in
  (* sort in reversed order since we're putting it on a list back to front *)
  let sortedList = List.sort (fun (k1,_) (k2,_) -> compare k2 k1) assocList in
  let newGlobals = List.fold_left
    (fun a (k,v) -> GText(Printf.sprintf "// %d -> %s" k v) :: a) f.globals sortedList in
  f.globals <- newGlobals
    

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
