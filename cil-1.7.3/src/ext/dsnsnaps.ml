(* See copyright notice at the end of this file *)

open Pretty
open Cil
open Trace
open Dsnutils
module E = Errormsg
module SS = Set.Make(String)

let snaps_file = "var_snapshots.txt"
let window_size = 2

let log_fn_name = "dsn_log"
let log_var_fn_name = "dsn_log_var"

(* we have a format string, and a list of expressions for the printf*)
type logStatement = string * exp list

let spaces = ref 0
let at_top_level () = !spaces <= 2
let incrIndent () = spaces := !spaces + 2
let decrIndent () = if !spaces <= 0 then E.s (E.bug "Negative indentation?");
                   spaces := !spaces - 2
let indent () =
  let rec f i = if i=0 then "" else f (i-1) ^ " " in f !spaces

let log_fn = makeGlobalVar log_fn_name
               (TFun(voidType, Some [("format", charPtrType, [])], true, []))
let log_var_fn = makeGlobalVar log_var_fn_name
               (TFun(voidType, Some [("format", charPtrType, [])], true, []))

let mkPrintVar (fmt: string) (args: exp list) : instr =
  Call(None, Lval(var log_var_fn), (mkString fmt)::args, locUnknown)

let mkPrintNoLoc ?(noindent=false) (fmt: string) (args: exp list) : instr =
  let spaces = if noindent then "" else indent () in
  Call(None, Lval(var log_fn), (mkString (spaces ^ fmt)) :: args, !currentLoc)

let mkPrint (fmt: string) (args: exp list) : instr =
  let lineStr (loc: location) =
    "#line "^ string_of_int loc.line ^" \""^ loc.file ^"\"" in
  let fmt' = (lineStr !currentLoc) ^"\n"^ indent () ^ fmt in
  mkPrintNoLoc ~noindent:true fmt' args

let stmtFromStmtList (stmts : stmt list) : stmt =
  mkStmt(Block(mkBlock (compactStmts stmts)))

(* Generates a logStatement (i.e., string output) that accurately describes
   an actual value considering its type. The string representation can directly
   be embedded in C code. *)
(* Structs will generate a string in the intiailization form, which can only
   be used in variable initialization. However, the support for struct is
   currently dropped. *)
let rec lossless_val ?(ptr_for_comp=false) (e: exp) =
  let typ = if ptr_for_comp then voidPtrType
                            else unrollType (typeOf e) in
  match typ with
  | TFloat _ -> E.s (E.unimp "TFloat not supported.")
  (* | TFloat _ -> ("%a", [e]) (* Hex representation is lossless. *) *)
  | TPtr _ -> ("%p", [e])
  | TEnum _ -> ("%d", [e])
  | TInt(ik, _) -> begin match ik with
    | IChar | ISChar | IBool | IInt | IShort | ILong | ILongLong -> ("%d", [e])
    | IUChar | IUInt | IUShort | IULong | IULongLong -> ("%u", [e]) end
(*
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
        E.s (E.unimp "Union not yet supported.")
*)
  | TComp _ -> E.s (E.unimp "Struct-copying is not supported. (%a)" d_exp e)
  | TArray _ -> E.s (E.bug "Looks like this yields a compiler error.")
  | TNamed _ -> E.s (E.bug "lossless_val: can't happen after unrollType.")
  | TVoid _ | TFun _ | TBuiltin_va_list _ ->
      E.s (E.bug "lossless_val: bug; can never be this type.")

let lossless_val_lv ?(ptr_for_comp=false) (lv: lval) =
  lossless_val ~ptr_for_comp (Lval lv)

(*
let rec d_mem_exp exp : logStatement =
  match exp with
  | Const(CStr _) | Const(CWStr _) -> E.s (E.bug "String not expected.")
  | Const _ -> (d_string "%a" d_exp exp, [])
  | UnOp(o,e,_) ->
      let opStr = d_string "%a " d_unop o in
      let (str,exp) = d_mem_exp e in
      (opStr ^"("^ str ^")", exp)

  | BinOp(op, e1, e2, t) -> begin match op with
    | IndexPI -> E.s (E.bug "IndexPI not expected.")
    | PlusPI | MinusPI ->
      let ut = unrollType t in
      (match ut with TPtr _ -> () | _ -> E.s (E.bug "Pointer type expected."));
      let sz_ptr = (bitsSizeOf ut) / 8 in
      let e2' = BinOp(Mult, e2, integer sz_ptr, t) in
      let op' = if op = PlusPI then PlusA else MinusA in
      d_mem_exp (BinOp(op', e1, e2', t))
    | MinusPP ->
      let ut = unrollType (typeOf e1) in
      (match ut with TPtr _ -> () | _ -> E.s (E.bug "Pointer type expected."));
      let sz_ptr = (bitsSizeOf ut) / 8 in
      let diff_e = BinOp(Div, BinOp(MinusA, e1, e2, t), integer sz_ptr, t) in
      d_mem_exp diff_e
    | _ -> let e1_s, e1_a = d_mem_exp e1 in
           let op_s = d_string " %a " d_binop op in
           let e2_s, e2_a = d_mem_exp e2 in
           ("("^ e1_s ^")"^ op_s ^"("^ e2_s ^")", e1_a @ e2_a) end

  | AddrOf _ | StartOf _ | Lval _ | CastE _
  | AlignOf _ | AlignOfE _ | SizeOf _ | SizeOfE _ | SizeOfStr _
  | Question _ | AddrOfLabel _ -> E.s (E.bug "Exp %a not expected." d_exp exp)
*)

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

(*
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
*)

(*
(* needed only for declaring unnamed args, e.g. function pointers *)
let rec d_unnamedArgsList lst  = match lst with
  | (s,t,a) :: [] ->
    let ((lhsStr,lhsArgs),(rhsStr,rhsArgs)) = d_logType t in
    (lhsStr ^ rhsStr,lhsArgs@rhsArgs)
  | (s,t,a) :: xs ->
    let ((lhsStr,lhsArgs),(rhsStr,rhsArgs)) = d_logType t in
    let thisStr = lhsStr ^ rhsStr in
    let thisArgs = lhsArgs @ rhsArgs in
    let (restStr,restArgs) = d_unnamedArgsList xs in
    (thisStr ^ ", " ^ restStr,thisArgs @ restArgs)
  | [] -> ("",[])
(* generate both a pre and a post part because we might have int a[2][3] *)
(* or a function pointer *)
and d_logType (tTop: typ) : (logStatement * logStatement) =
  match tTop with
    | TArray(t,eo,a) ->
      let ((lhsStr,lhsArgs),(rhsStr,rhsArgs)) = d_logType t in
      (*DSN should this be d_scope_exp??*)
      let e_str = match eo with
        | Some(e) -> d_string "%a" d_exp e
        | None -> ""
      in
      ((lhsStr,lhsArgs),
       ("[" ^ e_str ^ "]" ^ rhsStr,rhsArgs))
    | TPtr (TFun(retT,argsTLst,isVarArgs,_),_) ->
      (* DSN things might go crazy if we have return / take fn pointers.  Not worrying about that for now *)
      let retStr = d_string "%a" d_type retT in
      let (argsStr,argsArgs) = match argsTLst with
        | Some(l) -> d_unnamedArgsList l
        | None -> ("",[])
      in
      ((retStr ^ "( *" ,[]),
       (")(" ^ argsStr ^")",argsArgs))
    | _ -> let typeStr = d_string "%a" d_type tTop in
           ((typeStr,[]),
            ("",[]))

let d_decl (v : varinfo) : logStatement =
  let ((lhsStr,lhsArgs),(rhsStr,rhsArgs)) = d_logType v.vtype in
  ((lhsStr ^ " %s" ^ rhsStr),
   (lhsArgs @ [ mkString v.vname ] @ rhsArgs))

let mkVarDecl (v : varinfo) : instr =
  let (str,args) = d_decl v in
  mkPrintNoLoc (str ^ ";\n") args

let declareAllVars (slocals : varinfo list) : instr list =
  List.map mkVarDecl slocals
*)

let declareAllVarsStmt (slocals : varinfo list) : stmt =
  let pr_decl vi = mkPrintNoLoc ("long long "^ vi.vname ^";\n") [] in
  let instr_lst = List.map pr_decl slocals in
  mkStmt (Instr instr_lst)

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
let mk_print_orig (* For printing debugging info. *) = function
  | Set(lv, e, _) -> mkPrint (d_string "%a = %a;\n" d_lval lv d_exp e) []
  | Call(lv_o, e, al, _) ->
    let rec arg_lst = function [] -> ""
      | [x] -> (d_string "%a" d_exp x)
      | x::xs -> (d_string "%a, " d_exp x) ^ arg_lst xs in
    let fn_name = d_string "%a" d_exp e in
    let lhs = match lv_o with None -> ""
                            | Some lv -> d_string "%a =" d_lval lv in
    mkPrintNoLoc (lhs ^" "^ fn_name ^"("^ (arg_lst al) ^");\n") []
  | _ -> E.s (E.bug "Invalid usage.")

let local_vars = ref []

class dsnSnapsVisitorClass = object
  inherit nopCilVisitor

  val mutable return_seen = false
  val mutable window_id = 0
  val mutable num_asgns = window_size

  method vinst i = begin
    (*print_string (d_string "\n%a" d_instr i);*)
    let print_orig = mk_print_orig i in
    match i with
    | Set _ ->
      num_asgns <- num_asgns + 1;
      if num_asgns >= window_size && at_top_level () then begin
        let id = string_of_int window_id in
        window_id <- window_id + 1;
        num_asgns <- 0;

        let f vi (str, args) =
          let val_s, val_a = lossless_val_lv (Var vi, NoOffset) in
          ("("^ vi.vname ^" = "^ val_s ^ ") "^ str), (val_a @ args) in
        let str, args = List.fold_right f !local_vars ("", []) in
        let print_vars = mkPrintVar ("window "^ id ^": (and "^ str ^")\n\n")
                                    args in

        let call_marker = mkPrintNoLoc ("window("^ id ^");\n") [] in
        ChangeTo [call_marker; print_vars; print_orig; i]

      end else ChangeTo [print_orig; i]

    | Call _ -> ChangeTo [print_orig; i]

    | Asm _ -> E.s (E.bug "Not expecting assembly instructions.")
  end

  method vstmt (s : stmt) = begin
    if s.labels <> [] then E.s (E.bug "Cannot have labels.");
    match s.skind with
    | If(_, _, else_b, _) when else_b.bstmts = [] ->
        let postfn a =
          decrIndent ();
          match a.skind with
          | If(e, then_b, else_b, loc) when else_b.bstmts = [] ->
              let cond_s = d_string "if (%a){\n" d_exp e in
              then_b.bstmts <- compactStmts (
                [mkStmtOneInstr (mkPrint cond_s [])]
                @ then_b.bstmts
                @ [mkStmtOneInstr (mkPrintNoLoc "}\n" [])]);
              a
          | _ -> E.s (E.bug "If statement corrupted.") in
        incrIndent ();
        ChangeDoChildrenPost(s, postfn)
    | If _ -> E.s (E.bug "If statement with an else branch.")

    (* The only return we expect to see is the last return in 'main'. We add
       printf("} // main\n") just before the return to print the missing
       closing bracket for 'main.' *)
    | Return (e_opt, _) ->
        if return_seen = false then return_seen <- true
        else E.s (E.bug "There should be only one return for main.");
        let printCall = match e_opt with
            None   -> E.s (E.bug "main should return int.")
          | Some e -> mkPrint (d_string "return %a;\n} // main\n" d_exp e) [] in
        ChangeTo (stmtFromStmtList [mkStmtOneInstr printCall; s])

    | Instr _  | Block _ ->  DoChildren
    | Goto _ | ComputedGoto _ | Switch _ | Loop _ | TryFinally _ | TryExcept _
    | Break _ | Continue _ ->
        E.s (E.bug "Not expecting control flow statements.")
  end
end

let dsnSnapsVisitor = new dsnSnapsVisitorClass

let dsnSnaps (f: file) =

  let doGlobal = function
    | GFun (fdec, _) when fdec.svar.vname = "main" ->
        local_vars := fdec.slocals;

        incrIndent ();
        let allVarDeclaresStmt = declareAllVarsStmt fdec.slocals in
        let _ = visitCilFunction dsnSnapsVisitor fdec in
        decrIndent ();

        let main_head = mkStmt (Instr
          [mkPrint "int main(int argc, char **argv){\n" []]) in
        fdec.sbody <- mkBlock (compactStmts (
          [main_head; allVarDeclaresStmt; mkStmt (Block fdec.sbody)]))
    | GFun _ -> E.s (E.bug "Cannot have a function definition other than main.")
    | _ -> E.s (E.bug "main() should be the only global.")
  in
  Stats.time "dsn" (iterGlobals f) doGlobal;
  f.globals <- GVarDecl(log_fn, locUnknown) ::
               GVarDecl(log_var_fn, locUnknown) :: f.globals

let feature : featureDescr =
  { fd_name = "dsnsnaps";
    fd_enabled = Cilutil.dsnSnaps;
    fd_description = "Records values of variables at fixed intervals.";
    fd_extraopt = [];
    fd_doit = dsnSnaps;
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
