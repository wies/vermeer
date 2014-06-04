(* TODOS
 * remove the scope stuff
 * fix how indents work
 *)
(** See copyright notice at the end of this file *)

(** Add printf before each function call *)

open Pretty
open Cil
open Trace
module E = Errormsg
module H = Hashtbl

(* DSN - from logwrites.ml *)
(* David Park at Stanford points out that you cannot take the address of a
 * bitfield in GCC. *)

let printIndent = true
let indentSpaces = 2
let memPrefix = "_dsn_mem"

(* for future reference, how to add spaces in printf *)

(* we have a format string, and a list of expressions for the printf*)
type logStatement = string * exp list


(* Switches *)
let printFunctionName = ref "printf"

let addProto = ref false

let d_string (fmt : ('a,unit,doc,string) format4) : 'a = 
  let f (d: doc) : string = 
    Pretty.sprint 800 d
  in
  Pretty.gprintf f fmt 


let lineStr (loc: location) : string = 
  "#line " ^ string_of_int loc.line ^ " \"" ^ loc.file ^ "\"" 


let printf: varinfo option ref = ref None
let makePrintfFunction () : varinfo = 
    match !printf with 
      Some v -> v
    | None -> begin 
        let v = makeGlobalVar !printFunctionName 
                     (TFun(voidType, Some [("format", charPtrType, [])],
                             true, [])) in
        printf := Some v;
        addProto := true;
        v
    end


let mkPrintNoLoc (format: string) (args: exp list) : instr = 
  let p: varinfo = makePrintfFunction () in 
  Call(None, Lval(var p), (mkString format) :: args, !currentLoc)

let mkPrint (format: string) (args: exp list) : instr = 
  let p: varinfo = makePrintfFunction () in 
  let format = "%s\n" ^ format in
  let locArg = mkString (lineStr !currentLoc)  in
  let args = locArg :: args in
  Call(None, Lval(var p), (mkString format) :: args, !currentLoc)

let isGlobalVarLval (l : lval) = 
  let (host,off) = l in
  match host with 
  | Var(vinfo) -> vinfo.vglob
  | _ -> false 

let isGlobalVarExp (e : exp) = match e with
| Lval(l) -> isGlobalVarLval l
| _ -> false

let rec isLocalVarLval (l : lval) = 
  let (host,off) = l in
  match host with 
  | Var(vinfo) -> not vinfo.vglob
  | Mem(e) -> isLocalVarExp e 

and isLocalVarExp (e: exp) = match e with
| Lval(l) -> isLocalVarLval(l)
| _ -> false

let needsScopeId (e: exp) = isLocalVarExp e

let needsMemModelVarinfo (v : varinfo) = v.vaddrof

let needsMemModelLval (l : lval) = 
  match l with 
  | (host,off) -> begin 
      match host with 
      | Var(vinfo) -> needsMemModelVarinfo vinfo 
      | Mem(e) -> true
  end

(* DSN to finish *)
(* what happens if it is a pointer *)
let needsMemModel (e: exp) = 
  match e with 
  | Lval(l) -> needsMemModelLval(l)
  | _ -> false

(* Either create a reference to the stack variable
 * or the mem_0x1234 if that is needed 
 *)

(*DSN is it ok to use NoOffset here *)
let mkAddressVarinfo (v : varinfo) : exp = 
  let lv = (Var(v),NoOffset) in
  mkAddrOrStartOf lv

let mkAddress (e : exp) : exp = 
  match e with
  | Lval(l) -> mkAddrOrStartOf l
  | _ -> raise (Failure "expected an Lval here")

(* Returns true if the given lvalue offset ends in a bitfield access. *) 
let rec is_bitfield lo = match lo with
  | NoOffset -> false
  | Field(fi,NoOffset) -> not (fi.fbitfield = None)
  | Field(_,lo) -> is_bitfield lo
  | Index(_,lo) -> is_bitfield lo 

(* Return an expression that evaluates to the address of the given lvalue.
 * For most lvalues, this is merely AddrOf(lv). However, for bitfields
 * we do some offset gymnastics. 
 *)
let addr_of_lv (lh,lo) = 
  if is_bitfield lo then begin
    (* we figure out what the address would be without the final bitfield
     * access, and then we add in the offset of the bitfield from the
     * beginning of its enclosing comp *) 
    let rec split_offset_and_bitfield lo = match lo with 
      | NoOffset -> failwith "logwrites: impossible" 
      | Field(fi,NoOffset) -> (NoOffset,fi)
      | Field(e,lo) ->  let a,b = split_offset_and_bitfield lo in 
                        ((Field(e,a)),b)
      | Index(e,lo) ->  let a,b = split_offset_and_bitfield lo in
                        ((Index(e,a)),b)
    in 
    let new_lv_offset, bf = split_offset_and_bitfield lo in
    let new_lv = (lh, new_lv_offset) in 
    let enclosing_type = TComp(bf.fcomp, []) in 
    let bits_offset, bits_width = 
      bitsOffset enclosing_type (Field(bf,NoOffset)) in
    let bytes_offset = bits_offset / 8 in 
    let lvPtr = mkCast ~e:(mkAddrOf (new_lv)) ~newt:(charPtrType) in
    (BinOp(PlusPI, lvPtr, (integer bytes_offset), ulongType))
  end else (AddrOf (lh,lo)) 



let d_mem_lval (arg : lval) : logStatement = 
  if (needsMemModelLval arg) then (  memPrefix ^ "_%p", [mkAddrOrStartOf arg])
  else (d_string "%a" d_lval arg,[])

let rec d_mem_exp (arg :exp) : logStatement = 
  match arg with 
  | CastE(t,e) -> 
      let (str,arg) = d_mem_exp e in
      (d_string "(%a)(%s)" d_type t str,arg)
  | SizeOfE(e) -> 
      let (str,arg) = d_mem_exp e in
      (d_string "sizeof(%s) " str ,arg)
  | AlignOfE(e) ->
      let (str,arg) = d_mem_exp e in
      (d_string "__alignof__(%s)" str,arg)
  | UnOp(o,e,_) ->
      let opStr = d_string "%a " d_unop o in
      let (str,arg) = d_mem_exp e in
      (opStr ^ "(" ^ str ^ ")",arg)
  | BinOp(o,l,r,_) ->  
      let (lhsStr,lhsArg) = d_mem_exp l in
      let opStr = d_string " %a " d_binop o in
      let (rhsStr,rhsArg) = d_mem_exp r in
      ("(" ^ lhsStr ^ ")" ^ opStr ^ "(" ^ rhsStr ^ ")" ,lhsArg @ rhsArg)
  | AddrOf(l) -> ("%p",[addr_of_lv l])
  | StartOf(l) -> ("%p",[addr_of_lv l])  
  | _ -> 
      if (needsMemModel arg) then ( memPrefix ^ "_%p", [mkAddress arg] )
      else (d_string "%a" d_exp arg,[])
	  
let d_addr_exp (arg : exp ) : logStatement = 
  if (needsMemModel arg) then 
    match arg with 
    | Lval(host,off) -> 
	begin match host with
	| Var(vinfo) ->  (d_string "(%a == %%p)" d_exp (mkAddress arg), [mkAddress arg])
	| Mem(e) -> (d_string "(%a == %%p)" d_exp (arg), [mkAddress arg])
	end
    | _ -> raise (Failure "not possible")
  else raise (Failure "trying to print an unneeded address expression")


(* generate both a pre and a post part because we might have int a[2][3] *)
let rec mkTypeStr (t: typ) : (string * string) = 
  match t with 
 | TArray(t,eo,a) ->
      let (lhsStr,rhsStr) = mkTypeStr t in
 (*DSN should this be d_scope_exp??*)
      let e_str = match eo with
      | Some(e) -> d_string "%a" d_exp e
      | None -> ""
      in
      (lhsStr, "[" ^ e_str ^ "]" ^ rhsStr)
  | _ -> let typeStr = d_string "%a" d_type t in (typeStr,"")

(* I think there are a few cases we need to consider here
 * local variables
 * arrays
 * structures - or other larger than word sized things
 * pointers to simple memory
 * DSN TODO consider the harder cases at some point
 *) 
let mkVarDecl (v : varinfo) : instr = 
  let(lhsStr,rhsStr) = mkTypeStr v.vtype in
  if(needsMemModelVarinfo v) then
    mkPrintNoLoc "//%s %s%s %p;\n" 
      [ mkString lhsStr; 
	mkString v.vname; 
	mkString rhsStr;
	mkAddressVarinfo v
      ]
  else
    mkPrintNoLoc "%s %s%s;\n" 
      [ mkString lhsStr; 
	mkString v.vname; 
	mkString rhsStr
      ]
     
let rec declareAllVars (slocals : varinfo list) : instr list = 
  match slocals with
  | x :: xs -> (mkVarDecl x) :: (declareAllVars xs)
  | [] -> []

let declareAllVarsStmt (slocals : varinfo list) : stmt list =
  let instrs = declareAllVars slocals in
  let stmts = List.map (fun x -> mkStmtOneInstr x) instrs in
  compactStmts stmts

(* DSN perhaps there should be a common make print assgt function *)


(*DSN have to handle function pointers *)
let getFunctionVinfo e = match e with 
| Lval(Var(vinfo),_) -> vinfo
|_ -> raise (Failure "Not even an Lval.  Did you use function pointers?")
      
let getFormals e : (string * typ * attributes) list = 
  let vinfo = getFunctionVinfo e in 
  match vinfo.vtype with 
  | TFun(rtyp,args,varargs,attr) -> argsToList args
  | _ -> raise (Failure "Not a function")
	

(* DSN need a better name here *)
let rec mkActualArg (al : exp list) : logStatement = 
  match al with
  | [] -> ("",[])
  | x::[] -> d_mem_exp x
  | x::xs -> 
      let (thisStr,thisArg) = d_mem_exp x in
      let (restStr,restArgs) = mkActualArg xs in
      (thisStr ^ ", " ^ restStr, thisArg @ restArgs)




let isDefinedFn e =
  let vinfo = getFunctionVinfo e in
  match vinfo.vstorage with 
  | Extern -> false 
  | _ ->  not (Hashtbl.mem builtinFunctions vinfo.vname)

let i = ref 0
let name = ref ""


let currentFunc: string ref = ref ""

class dsnconcreteVisitorClass = object
  inherit nopCilVisitor

  val printfFun =   
    let fdec = emptyFunction "printf" in
    fdec.svar.vtype <- TFun(intType, 
                            Some [("format", charConstPtrType, []) ], 
                            true, []);
    fdec

  (* Watch for a declaration for our printer *)
  
  method vinst i = begin
    match i with
      Set(lv, e, l) -> 
	let typStr = "/* " 
	  ^ (d_string "%a" d_type (typeOfLval lv)) 
	  ^ "*/ " in
	let (lhsStr,lhsArg) = d_mem_lval lv in
(* assume that we only have reduced expressions at this point!  Should maybe put an assert
of that here? *)
(* DSN Does anything go weird if we have function pointers *)
	let (rhsStr,rhsArg) = d_mem_exp e in
	let printStr = typStr ^ lhsStr ^  " = " ^ rhsStr ^ ";\n" in
	let printArgs = lhsArg @ rhsArg in
	let printCall = mkPrint printStr printArgs in
	let newInstrs =  printCall :: [i] in
	ChangeTo newInstrs
    | Call(lo,e,al,l) ->
(* The only calls that can occur in a reduced format are to functions
 * where we do not have the implementation.  So just store the final value
 *) 
	let (lhsStr,lhsArg) = 
	  match lo with
	  | Some(lv) -> let (s,a) = d_mem_lval lv in (s ^ " = ",a)
	  | None -> ("",[])
	in
	let fnName = d_string "%a" d_exp e in
	let (argsStr, argsArgs) = mkActualArg al in
	let callStr = lhsStr ^ fnName ^ "(" ^ argsStr ^ ");\n" in
	let callArgs = lhsArg @ argsArgs in
	let printCall = mkPrint callStr callArgs in
	ChangeTo [ printCall; i] 
    | _ -> DoChildren
  end
  method vstmt (s : stmt) = begin
    match s.skind with
    | _ -> DoChildren
  end
end

let dsnconcreteVisitor = new dsnconcreteVisitorClass

let dsnconcrete (f: file) : unit =

  let doGlobal = function
      
    | GVarDecl (v, _) when v.vname = !printFunctionName -> 
        if !printf = None then
          printf := Some v 
    | GFun (fdec, loc) ->
        currentFunc := fdec.svar.vname;
        (* do the body *)
        ignore (visitCilFunction dsnconcreteVisitor fdec);
	
        (* Now add the entry instruction *)
        let pre = if !currentFunc = "main" then 
	  [mkStmtOneInstr (mkPrint  "int main(int argc, char** argv){\n" [])]
	else 
	  [mkStmtOneInstr (mkPrint (d_string "//enter %s\n" !currentFunc) [])] 
	in 
        fdec.sbody <- 
          mkBlock (compactStmts (pre @ 
				 (declareAllVarsStmt fdec.slocals) @
				 [mkStmt (Block fdec.sbody) ]
				   ))
    | _ -> ()
  in
  Stats.time "dsn" (iterGlobals f) doGlobal;
  if !addProto then begin
    let p = makePrintfFunction () in 
    E.log "Adding prototype for call logging function %s\n" p.vname;
    f.globals <- 
      GVarDecl (p, locUnknown) ::
      f.globals
  end  

let feature : featureDescr = 
  { fd_name = "dsnconcrete";
    fd_enabled = Cilutil.dsnConcrete;
    fd_description = "generation of code to log function calls";
    fd_extraopt = [];
    fd_doit = dsnconcrete;
    fd_post_check = true
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
