(* See copyright notice at the end of this file *)

(* The translation can never be perfect. For example, bizarre low-level memory
   manipulation will mostly not be handled proplery:

     int x = 0xFFFF;
     *(char * )&x = 0;
*)

open Pretty
open Cil
open Trace
module E = Errormsg
module SS = Set.Make(String)

(* DSN - from logwrites.ml *)
(* David Park at Stanford points out that you cannot take the address of a
 * bitfield in GCC. *)

let memPrefix = "_dsn_mem"
let wrapper_postfix = "_dsn_wrapper"
let log_fn_name = "dsn_log"

let preset_wrappers = ["read";
                       "memset"; "strcpy"; "strncpy";
                       "sprintf";
                       "getoptlong"]

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
  let f (d: doc) : string = Pretty.sprint 800 d in
  Pretty.gprintf f fmt

let argc_argv_handler =
  makeGlobalVar "main_argc_argv_dsn_printer"
    (TFun(voidType, Some [("p_argc", intPtrType, []);
                          ("argv", TPtr(TPtr(charPtrType, []), []), [])],
          false, []))

let log_fn = makeGlobalVar log_fn_name
               (TFun(voidType, Some [("format", charPtrType, [])], true, []))

let mkPrintNoLoc ?noindent (fmt: string) (args: exp list) : instr =
  let spaces = if noindent = None then indent () else "" in
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
let rec lossless_val ?ptr_for_comp (lv: lval) : logStatement =
  let e = Lval(lv) in
  let typ = if ptr_for_comp = None then unrollType (typeOfLval lv)
                                   else voidPtrType in
  match typ with
  | TFloat _ -> ("%a", [e]) (* Hex representation is lossless. *)
  | TPtr _ -> ("%p", [e])
  | TEnum _ -> ("%d", [e])
  | TInt(ik, _) -> (match ik with
    | IChar | ISChar | IBool | IInt | IShort | ILong | ILongLong -> ("%d", [e])
    | IUChar | IUInt | IUShort | IULong | IULongLong -> ("%u", [e]))

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
        E.s (E.bug "Union not yet supported.")
*)
  | TComp _ -> E.s (E.bug "Struct-copying is not supported.")
  | TArray _ -> E.s (E.bug "Looks like this yields a compiler error.")
  | TNamed _ -> E.s (E.bug "lossless_val: can't happen after unrollType.")
  | TVoid _ | TFun _ | TBuiltin_va_list _ ->
      E.s (E.bug "lossless_val: bug; can never be this type.")

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
(*let mkAddressVarinfo (v : varinfo) : exp =
  let lv = (Var(v),NoOffset) in
  mkAddrOrStartOf lv*)

(*let mkAddress (e : exp) : exp =
  match e with
  | Lval(l) -> mkAddrOrStartOf l
  | _ -> raise (Failure "expected an Lval here")*)

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



let d_mem_lval ?pr_val (lv : lval) : logStatement =
  if (needsMemModelLval lv) then
    let typ_str = d_string "%a" d_type (unrollTypeDeep (typeOfLval lv)) in
    let val_s, val_a = if pr_val = None then "", []
      else let s, a = lossless_val ~ptr_for_comp:true lv in "|val: "^ s, a in
    ((memPrefix ^"_%p/*|"^ typ_str ^ val_s ^"|*/"),
     [mkAddrOrStartOf lv] @ val_a)
  else (d_string "%a" d_lval lv,[])

let to_c_string ocaml_str =
  let len = String.length ocaml_str in
  let rec trans i acc =
    if i = len then acc
    else let char_str = Printf.sprintf "\\%o" (int_of_char ocaml_str.[i]) in
         trans (i+1) (acc ^ char_str) in
  "\""^ (trans 0 "") ^ "\""

let rec d_simp_exp arg : logStatement =
  match arg with
  | Const(CStr s) -> to_c_string s, []
    (* Bug: e.g., \031 in OCaml string is base 10.
    "\"%s\"", [mkString (String.escaped s)]*)
  | Const(CWStr s) -> E.s (E.bug "CWStr not supported.")
  | Const _ | Lval _ -> (d_string "%a" d_exp arg,[])
  | CastE(t,e) ->
      let (str,arg) = d_simp_exp e in
      (d_string "(%a)(%s)" d_type t str, arg)
  | UnOp(o,e,_) ->
      let opStr = d_string "%a " d_unop o in
      let (str,arg) = d_simp_exp e in
      (opStr ^"("^ str ^")", arg)
  | BinOp(o,l,r,_) ->
      let (lhsStr,lhsArg) = d_simp_exp l in
      let opStr = d_string " %a " d_binop o in
      let (rhsStr,rhsArg) = d_simp_exp r in
      ("("^ lhsStr ^")"^ opStr ^"("^ rhsStr ^")", lhsArg @ rhsArg)
  | AddrOf(l)
  | StartOf(l) -> ("%p", [addr_of_lv l])

  | AlignOf _ | AlignOfE _ -> E.s (E.bug "__alignof__() not expected.")
  | SizeOf _ | SizeOfE _ | SizeOfStr _ -> E.s (E.bug "sizeof() not expected.")
  | Question _ -> E.s (E.bug "Question exp not expected.")
  | AddrOfLabel _ -> E.s (E.bug "AddrOfLabel not expected.")

let rec has_str_lit = function
  | Const(CStr _) | Const(CWStr _) -> true
  | Const _ -> false
  | CastE(_, e) -> has_str_lit e
  | UnOp(_, e, _) -> has_str_lit e
  | BinOp(_, l, r,_) -> has_str_lit l || has_str_lit r

  | Lval lv | AddrOf lv | StartOf lv -> (match lv with
    | (Var _, _) -> false | (Mem e, _) -> has_str_lit e)

  | AlignOf _ | AlignOfE _ -> E.s (E.bug "__alignof__() not expected.")
  | SizeOf _ | SizeOfE _ | SizeOfStr _ -> E.s (E.bug "sizeof() not expected.")
  | Question _ -> E.s (E.bug "Question exp not expected.")
  | AddrOfLabel _ -> E.s (E.bug "AddrOfLabel not expected.")

let rec d_mem_exp ?pr_val (arg :exp) : logStatement =
  let pv = pr_val <> None in
  match arg with
  | Lval lv -> d_mem_lval ~pr_val:pv lv
  | Const(CStr s) -> to_c_string s, []
    (* TODO Bug: e.g., \031 in OCaml string is base 10.
    "\"%s\"", [mkString (String.escaped s)] *)
  | Const(CWStr s) -> E.s (E.bug "CWStr not supported.")
  | Const _ -> (d_string "%a" d_exp arg, [])
  | CastE(t,e) ->
      let (str,arg) = d_mem_exp ~pr_val:pv e in
      (d_string "(%a)(%s)" d_type t str, arg)
  | UnOp(o,e,_) ->
      let opStr = d_string "%a " d_unop o in
      let (str,arg) = d_mem_exp ~pr_val:pv e in
      (opStr ^"("^ str ^")", arg)
  | BinOp(o,l,r,_) ->
      let (lhsStr,lhsArg) = d_mem_exp ~pr_val:pv l in
      let opStr = d_string " %a " d_binop o in
      let (rhsStr,rhsArg) = d_mem_exp ~pr_val:pv r in
      ("("^ lhsStr ^")"^ opStr ^"("^ rhsStr ^")", lhsArg @ rhsArg)
  | AddrOf(l)
  | StartOf(l) -> ("%p", [addr_of_lv l])

  | AlignOf _ | AlignOfE _ -> E.s (E.bug "__alignof__() not expected.")
  | SizeOf _ | SizeOfE _ | SizeOfStr _ -> E.s (E.bug "sizeof() not expected.")
  | Question _ -> E.s (E.bug "Question exp not expected.")
  | AddrOfLabel _ -> E.s (E.bug "AddrOfLabel not expected.")

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
      ((retStr ^ "(*" ,[]),
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

let rec declareAllVars (slocals : varinfo list) : instr list =
  List.map mkVarDecl slocals

let declareAllVarsStmt (slocals : varinfo list) : stmt =
  mkStmt (Instr (declareAllVars slocals))

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


let mk_print_orig (* For printing debugging info. *) = function
  | Set(lv, e, _) ->
    let orig_rhs_s, orig_a = d_simp_exp e in
    let orig_s = (d_string "/* %a = " d_lval lv) ^ orig_rhs_s ^ "; */\n" in
    mkPrint orig_s orig_a
  | _ -> E.s (E.bug "Invalid usage.")

(* Is this a string literal assignment? If yes, we need to assign an actual
   address directly. Don't worry though; memory variables affected by this
   entire string will be covered by 'postprocess_concrete.' *)
let is_str_lit_asgn = function
  | CastE(_, Const(CStr s)) | Const(CStr s) -> true
  | e -> if has_str_lit e then (* Checking if there can be other forms. *)
           E.s (E.bug "Unexpected assignemnt involving string literals.");
         false

class dsnconcreteVisitorClass = object
  inherit nopCilVisitor

  val mutable return_seen = false

  method vinst i = begin
    match i with
      Set(lv, e, l) ->
        (* DSN Does anything go weird if we have function pointers *)
	let (lhsStr,lhsArg) = d_mem_lval lv in
        let (rhsStr,rhsArg) = d_mem_exp ~pr_val:true e in

        (* Delay printing the right-hand side until after execution if we need
           to assign the result directly instead of using the RHS exp. *)
        let special_cases =
          (rhsStr = "stdin" or rhsStr = "stdout" or rhsStr = "stderr") in
        let actual_val = (is_str_lit_asgn e) or special_cases in

        let pr_s, pr_a = if actual_val
                         then (lhsStr ^" = "              , lhsArg)
                         else (lhsStr ^" = "^ rhsStr ^"; ", lhsArg @ rhsArg) in
        let print_asgn = mkPrintNoLoc pr_s pr_a in

        (* For debugging, print the actual value assigned too. *)
        let val_s, val_a = lossless_val lv in
        let pr_s, pr_a = "/* Assigned: "^ val_s ^" */\n", val_a in
        (* Assign an actual value assigned if needed. *)
        let pr_s', pr_a' = if not actual_val then pr_s, pr_a
          else val_s ^"; "^ pr_s, val_a @ val_a in
        let print_asgn_post = mkPrintNoLoc ~noindent:true pr_s' pr_a' in

        let print_orig = mk_print_orig i in (* For printing debugging info. *)
	let newInstrs =  [print_orig; print_asgn; i; print_asgn_post] in
	ChangeTo newInstrs

    (* The only calls that can occur in a reduced format are to functions
       where we do not have the implementation. *)
    | Call(lo,e,al,l) ->
        let lhs_s, lhs_a = match lo with None -> "", []
                                       | Some(lv) -> d_mem_lval lv in

        (* Let's record the call in a comment too. *)
        let fn_name = d_string "%a" d_exp e in
	let (argsStr, argsArgs) = mkActualArg al in
        let lhs_cs =
          if lhs_s = "" then "(no return or ignored) " else lhs_s ^ " = " in
	let cmnt_str = "/* Call: "^ lhs_cs ^ fn_name ^"("^ argsStr ^") */\n" in
	let cmnt_args = lhs_a @ argsArgs in
        let cmntPrintCall = mkPrint cmnt_str cmnt_args in

	let printCalls = match lo with
	  | None -> [] (* No assignment; nothing to print. *)
	  | Some(lv) ->
              (* Print the actual return value stored in the left-hand side
                 variable in a lossless representation. *)
              let val_s, val_a = lossless_val lv in
              [mkPrintNoLoc (lhs_s ^" = "^ val_s ^";\n") (lhs_a @ val_a)]
              (* Support for struct-copying returns disabled. Take a look at
                 'loosless_val' function.
              (* Declaring a tmp variable is a trick to use an initialization
                 form (e.g., { { 65, 66 }, 9 } for a struct). *)
              let typ_str = d_string "%a" d_type (typeOfLval lv) in
              [mkPrintNoLoc ("{ "^ typ_str ^" dsn_tmp_ret = "^ val_s ^";\n")
                            val_a;
               mkPrintNoLoc ("  "^ lhs_s ^" = dsn_tmp_ret; }\n") lhs_a] *) in
	ChangeTo (i :: cmntPrintCall :: printCalls)
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
              let eStr, eArg = d_mem_exp ~pr_val:true e in
              let fStr = "if("^ eStr ^"){\n" in
              then_b.bstmts <- compactStmts (
		[mkStmtOneInstr (mkPrint fStr eArg)]
		@ then_b.bstmts
                @ [mkStmtOneInstr (mkPrintNoLoc "}\n" [])]);
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

    | Instr _  | Block _ ->  DoChildren
    | Goto _ | ComputedGoto _ | Switch _ | Loop _ | TryFinally _ | TryExcept _
    | Break _ | Continue _ ->
        E.s (E.bug "Not expecting control flow statements.")
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

        (* We want to inject a function call right after the start of main
           that will setup proper assignments for given argc and argv values. *)
        let argc_argv_handler_call =
          let argc_vi, argv_vi = match fdec.sformals with
            | [x; y] -> x, y | _ -> E.s (E.bug ("Where's argc or argv?")) in
          let p_argc_e = mkAddrOrStartOf (var argc_vi) in
          let p_argv_e = mkAddrOrStartOf (var argv_vi) in
          Call(None, Lval(var argc_argv_handler),
                     [p_argc_e; p_argv_e], locUnknown) in

        let stmt = mkStmt (Instr
          [Call(None, Lval(var globalDeclFn.svar), [], locUnknown);
	   mkPrint ("int main(int argc, char** argv){" ^
                    "/* Parameters should not be used. */\n") [];
           argc_argv_handler_call]) in
        fdec.sbody <- mkBlock
          [stmt; allVarDeclaresStmt; mkStmt (Block fdec.sbody)]

    | GFun _ -> E.s (E.bug "Cannot have a function definition other than main.")
    | _ -> ()
  in
  Stats.time "dsn" (iterGlobals f) doGlobal;
  E.log "Adding prototype for call logging function %s\n" log_fn.vname;
  f.globals <-
    GVarDecl (log_fn, locUnknown) ::
    GVarDecl (argc_argv_handler, locUnknown) ::
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
