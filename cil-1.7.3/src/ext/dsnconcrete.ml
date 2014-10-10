(* TODOS
 * remove the scope stuff
 * fix how indents work
 *)
(** See copyright notice at the end of this file *)

(* The translation is never perfect. For example, bizarre low-level memory
   manipulation is mostly not handled proplery:

     int x = 0xFFFF;
     *(char * )&x = 0;
*)

open Pretty
open Cil
open Trace
module E = Errormsg
module H = Hashtbl
module SS = Set.Make(String)

(* DSN - from logwrites.ml *)
(* David Park at Stanford points out that you cannot take the address of a
 * bitfield in GCC. *)

let memPrefix = "_dsn_mem"
let wrapper_postfix = "_dsn_wrapper"
let log_fn_name = "dsn_log"

let preset_wrappers = ["sprintf"]

let wrapper_set = List.fold_right SS.add preset_wrappers SS.empty

let printIndent = true
let indentSpaces = 2
let spaces = ref 0
let incrIndent () = spaces := !spaces + indentSpaces
let decrIndent () = if !spaces <= 0 then E.s (E.bug "Negative indentation?");
                   spaces := !spaces - indentSpaces
let indent () =
  let rec f i = if i=0 then "" else f (i-1) ^ " " in f !spaces


(* we have a format string, and a list of expressions for the printf*)
type logStatement = string * exp list

let d_string (fmt : ('a,unit,doc,string) format4) : 'a =
  let f (d: doc) : string =
    Pretty.sprint 800 d
  in
  Pretty.gprintf f fmt

let log_fn = makeGlobalVar log_fn_name
               (TFun(voidType, Some [("format", charPtrType, [])], true, []))

let mkPrintNoLoc ?noindent (format: string) (args: exp list) : instr =
  let spaces = match noindent with None -> indent () | _ -> "" in
  Call(None, Lval(var log_fn), (mkString (spaces ^ format)) :: args, !currentLoc)

let mkPrint (format: string) (args: exp list) : instr =
  let lineStr (loc: location) =
    "#line "^ string_of_int loc.line ^" \""^ loc.file ^"\"" in
  let format = (lineStr !currentLoc) ^"\n"^ indent () ^ format in
  mkPrintNoLoc ~noindent:true format args

let stmtFromStmtList (stmts : stmt list) : stmt =
  mkStmt(Block(mkBlock (compactStmts stmts)))

(*
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
*)

let needsMemModelVarinfo (v : varinfo) = v.vaddrof

let needsMemModelLval (l : lval) =
  match l with
    | (Var(vinfo), off) ->  needsMemModelVarinfo vinfo
    | _ -> true


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
let addr_of_lv (lh,lo) : exp =
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
  end else (*mkAddrOrStartOf (lh,lo)*)
           (AddrOf (lh,lo))



let d_mem_lval (arg : lval) : logStatement =
  if (needsMemModelLval arg) then (  memPrefix ^"_%p", [mkAddrOrStartOf arg])
  else (d_string "%a" d_lval arg,[])

let rec d_mem_exp (arg :exp) : logStatement =
  match arg with
  | Const(CStr(s)) -> ("\"%s\"",[mkString (String.escaped s)])
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
      (opStr ^"("^ str ^")",arg)
  | BinOp(o,l,r,_) ->
      let (lhsStr,lhsArg) = d_mem_exp l in
      let opStr = d_string " %a " d_binop o in
      let (rhsStr,rhsArg) = d_mem_exp r in
      ("("^ lhsStr ^")"^ opStr ^"("^ rhsStr ^")" ,lhsArg @ rhsArg)
  | AddrOf(l) -> ("%p",[addr_of_lv l])
  | StartOf(l) -> ("%p",[addr_of_lv l])

  | Question _ -> E.s (E.bug "Question should have been eliminated.")
  | AddrOfLabel _ -> E.s (E.bug "AddrOfLabel should have been eliminated.")

  | _ ->
      if (needsMemModel arg) then ( memPrefix ^"_%p", [mkAddress arg] )
      else (d_string "%a" d_exp arg,[])

(*
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
*)

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
      (lhsStr, "["^ e_str ^"]"^ rhsStr)
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
  List.map mkVarDecl slocals

let declareAllVarsStmt (slocals : varinfo list) : stmt list =
  let instrs = declareAllVars slocals in
  let stmts = List.map mkStmtOneInstr instrs in
  compactStmts stmts

(* DSN perhaps there should be a common make print assgt function *)

(*
(*DSN have to handle function pointers *)
let getFunctionVinfo e = match e with
| Lval(Var(vinfo),_) -> vinfo
|_ -> raise (Failure "Not even an Lval.  Did you use function pointers?")

let getFormals e : (string * typ * attributes) list =
  let vinfo = getFunctionVinfo e in
  match vinfo.vtype with
  | TFun(rtyp,args,varargs,attr) -> argsToList args
  | _ -> raise (Failure "Not a function")

let isDefinedFn e =
  let vinfo = getFunctionVinfo e in
  match vinfo.vstorage with
  | Extern -> false
  | _ ->  not (Hashtbl.mem builtinFunctions vinfo.vname)
*)

(* DSN need a better name here *)
let rec mkActualArg (al : exp list) : logStatement =
  match al with
  | [] -> ("",[])
  | x::[] -> d_mem_exp x
  | x::xs ->
      let (thisStr,thisArg) = d_mem_exp x in
      let (restStr,restArgs) = mkActualArg xs in
      (thisStr ^", "^ restStr, thisArg @ restArgs)

let rec lossless_val (lv: lval) : logStatement =
  let e = Lval(lv) in
  match unrollType (typeOfLval lv) with
  | TFloat _ -> ("%a", [e]) (* Hex representation is lossless. *)
  | TPtr _ -> ("%p", [e])
  (* TODO: I don't think so, but should we care about IULong, etc? *)
  | TInt _ | TEnum _ -> ("%d", [e])

  | TComp (ci, _) ->
      let lhost, offset = lv in
      let new_offset f = addOffset (Field(f, NoOffset)) offset in
      if ci.cstruct then (* If not a union, iterate over all fields. *)
        let rec iter_fields (str, args) = function
          | [] -> E.s (E.bug "lossless_val: struct having no field?")
          | [f] -> let s, a = lossless_val (lhost, new_offset f) in
                   (str ^ s ^" }", args @ a)
          | f::fs -> let s, a = lossless_val (lhost, new_offset f) in
                     iter_fields (str ^ s ^", ", args @ a) fs in
        iter_fields ("{ ", []) ci.cfields
      else (* TODO: for a union, need to identify a biggest-size field. *)
        E.s (E.bug "Union not yet supported.")

  | TArray _ -> E.s (E.bug "Look like this yields a compiler error.")
  | TNamed _ -> E.s (E.bug "lossless_val: can't happen after unrollType.")
  | TVoid _ | TFun _ | TBuiltin_va_list _ ->
      E.s (E.bug "lossless_val: bug; can never be this type.")

class dsnconcreteVisitorClass = object
  inherit nopCilVisitor

  val mutable return_seen = false

  method vinst i = begin
    match i with
      Set(lv, e, l) ->
	let typStr = "/* "^ (d_string "%a" d_type (typeOfLval lv)) ^" */ " in
	let (lhsStr,lhsArg) = d_mem_lval lv in
(* assume that we only have reduced expressions at this point!  Should maybe put an assert
of that here? *)
(* DSN Does anything go weird if we have function pointers *)
	let (rhsStr,rhsArg) = d_mem_exp e in
	let printStr = typStr ^ lhsStr ^" = "^ rhsStr ^";\n" in
	let printArgs = lhsArg @ rhsArg in
	let printCall = mkPrint printStr printArgs in
	let newInstrs =  printCall :: [i] in
	ChangeTo newInstrs
    | Call(lo,e,al,l) ->
(* The only calls that can occur in a reduced format are to functions where
   we do not have the implementation. *)
        (* Let's record the call in a comment too. *)
        let fn_name = d_string "%a" d_exp e in
	let (argsStr, argsArgs) = mkActualArg al in
	let comment_str = "/* Called "^ fn_name ^"("^ argsStr ^"). */\n" in
	let comment_args = argsArgs in
        let printCall' = mkPrint comment_str comment_args in

	let printCalls = match lo with
	  | None -> [] (* No assignment; nothing to print. *)
	  | Some(lv) ->
              (* Print the actual return value stored in the left-hand side
                 variable in a lossless representation. *)
              let val_s, val_a = lossless_val lv in
              let lhs_s, lhs_a = d_mem_lval lv in
              let typ_str = d_string "%a" d_type (typeOfLval lv) in

              (* Declaring a tmp variable is a trick to use an initialization
                 form (e.g., { { 65, 66 }, 9 } for a struct). *)
              [mkPrintNoLoc ("{ "^ typ_str ^" dsn_tmp_ret = "^ val_s ^";\n")
                            val_a;
               mkPrintNoLoc ("  "^ lhs_s ^" = dsn_tmp_ret; }\n") lhs_a] in
	ChangeTo (i :: printCall' :: printCalls)
    | _ -> DoChildren
  end
  method vstmt (s : stmt) = begin
    if s.labels <> [] then E.s (E.bug "Cannot have labels.");
    match s.skind with
    | If(_, _, else_b, _) when else_b.bstmts = [] ->
        let postfn a =
          decrIndent ();
          match a.skind with
          | If(e, then_b, else_b, loc) when else_b.bstmts = [] ->
              let eStr, eArg = d_mem_exp e in
              let fStr = "if("^ eStr ^"){\n" in
              then_b.bstmts <- [mkStmtOneInstr (mkPrint fStr eArg)]
                               @ then_b.bstmts @
                               [mkStmtOneInstr (mkPrintNoLoc "}\n" [])];
              a
          | _ -> E.s (E.bug "If statement corrupted.") in
        incrIndent ();
        ChangeDoChildrenPost (s, postfn)
    | If _ -> E.s (E.bug "If statement with an else branch.")

    (* The only return we expect to see is the last return in 'main'. We add
       printf("} // main\n") just before the return to print the missing
       closing bracket for 'main.' *)
    | Return (e_opt, _) ->
        if return_seen = false then return_seen <- true
        else E.s (E.bug "There should be only one return for main.");
        let printCall = match e_opt with
            None   -> mkPrint "return;\n} // main\n" []
          | Some e -> mkPrint (d_string "return %a;\n} // main\n" d_exp e) [] in
        ChangeTo (stmtFromStmtList [mkStmtOneInstr printCall; s])

    | Instr(Set(lv, e, _)::_) ->
        (* Output for inspection purpose. *)
        ignore (Pretty.printf "DBG: Instr(Set(%a, %a, _))\n" d_lval lv d_exp e);
        DoChildren
    | Instr(Call(_, e, _, _)::_) ->
        (* Output for inspection purpose. *)
        ignore (Pretty.printf "DBG: Instr(Call(_, %a, _))\n" d_exp e);
        DoChildren

    | Instr _ -> E.s (E.bug "Not expecting assembly instructions.")

    | Goto _ | ComputedGoto _ | Switch _ | Loop _ | TryFinally _ | TryExcept _
    | Break _ | Continue _ ->
        E.s (E.bug "Not expecting control flow statements.")

    | Block _ -> DoChildren
  end
end

let dsnconcreteVisitor = new dsnconcreteVisitorClass

let globalDeclFn =
  let fdec = emptyFunction "__globalDeclFn" in
  let typ = TFun(voidType, Some[], false, []) in
  let _  = setFunctionType fdec typ  in
  fdec


let dsnconcrete (f: file) : unit =

  let doGlobal (g: global) =
    (* Some helper functions. *)
    let isFunc (v: varinfo) = match v.vtype with TFun _ -> true | _ -> false in
    let declareFn (g: global) =
      let arg = mkString (d_string "%a" d_global g) in
      globalDeclFn.sbody <-
        mkBlock (compactStmts [mkStmt (Block globalDeclFn.sbody);
                               mkStmtOneInstr (mkPrintNoLoc "%s" [arg])]) in

    match g with
    | GVarDecl (v, _) | GVar (v, _, _) when isFunc v ->
        (* If this surviving function requires a wrapper, change its name to
           point to the wrapper. Otherwise, don't bother printing anything. *)
        if SS.exists (fun x -> x = v.vname) wrapper_set
        then v.vname <- v.vname ^ wrapper_postfix
    | GVarDecl _ | GVar _ | GType _ | GCompTag _ | GEnumTag _ -> declareFn g

    | GFun (fdec, _) when fdec.svar.vname = "main" ->
        incrIndent ();
        let allVarDeclaresStmt = declareAllVarsStmt fdec.slocals in
        ignore (visitCilFunction dsnconcreteVisitor fdec);
        decrIndent ();

        let stmts = List.map mkStmtOneInstr
          [Call(None,Lval(var globalDeclFn.svar),[],locUnknown);
	   mkPrint "int main(int argc, char** argv){\n" []] in
        fdec.sbody <-
          mkBlock (compactStmts (stmts @ allVarDeclaresStmt @
				 [mkStmt (Block fdec.sbody)]))

    | GFun _ -> E.s (E.bug "Cannot have a function definition other than main.")
    | _ -> ()
  in
  Stats.time "dsn" (iterGlobals f) doGlobal;
  E.log "Adding prototype for call logging function %s\n" log_fn.vname;
  f.globals <-
    GVarDecl (log_fn, locUnknown) ::
    GFun (globalDeclFn, locUnknown) :: (*should be declared last*)
    f.globals

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
