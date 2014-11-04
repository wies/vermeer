(* See copyright notice at the end of this file *)

(* The translation can never be perfect. For example, bizarre low-level memory
   manipulation will mostly not be handled proplery:

     int x = 0xFFFF;
     *(char * )&x = 0;
*)

(* The type conversion to signed long long is not perfect. For example,
   overflow may happen. *)

(* TODO We could add fine-grained support for memory-region initialization
   (e.g., array, struct initialization). Currently, they are simply removed
   in this pass (safe to do so, since such variables are not referenced
   directly), and the initialization is handled in the postprocess_concrete
   process. They way postprocess_concrete works is that whenever an
   uninitialized memory (_dsn_mem_0x...) variables are first accessed, the
   script extracts the run-time value of the variable and adds an intialization
   in the memory variable declaration. *)

open Pretty
open Cil
open Trace
module E = Errormsg
module SS = Set.Make(String)

(* DSN - from logwrites.ml *)
(* David Park at Stanford points out that you cannot take the address of a
 * bitfield in GCC. *)

let memPrefix = "_dsn_mem"
let wrapper_fn_postfix = "_dsn_wrapper"
let log_fn_name = "dsn_log"

let preset_wrappers = ["read";
                       "memset"; "strcpy"; "strncpy";
                       "sprintf";
                       "getopt_long"]

let wrapper_fn_set = List.fold_right SS.add preset_wrappers SS.empty

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
let rec lossless_val ?ptr_for_comp:(ptr_for_comp=false) (e: exp) =
  let typ = if ptr_for_comp then voidPtrType
                            else unrollType (typeOf e) in
  match typ with
  | TFloat _ -> E.s (E.bug "TFloat not supported.")
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
        E.s (E.bug "Union not yet supported.")
*)
  | TComp _ -> E.s (E.bug "Struct-copying is not supported.")
  | TArray _ -> E.s (E.bug "Looks like this yields a compiler error.")
  | TNamed _ -> E.s (E.bug "lossless_val: can't happen after unrollType.")
  | TVoid _ | TFun _ | TBuiltin_va_list _ ->
      E.s (E.bug "lossless_val: bug; can never be this type.")

let lossless_val_lv ?ptr_for_comp:(ptr_for_comp=false) (lv: lval) =
  lossless_val ~ptr_for_comp:ptr_for_comp (Lval lv)
  
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
    E.s (E.bug "Stopping here for debugging.")
(*
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
*)
  end else (*mkAddrOrStartOf (lh,lo)*)
           (AddrOf (lh,lo))

let d_mem_lval ?pr_val (lv : lval) : logStatement =
  if (needsMemModelLval lv) then
    let typ_str = d_string "%a" d_type (unrollTypeDeep (typeOfLval lv)) in
    let val_s, val_a = if pr_val = None then "", []
      else let s, a = lossless_val_lv ~ptr_for_comp:true lv in "|val: "^ s, a in
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

let rec strip_cast exp =
  let strip_cast_lv lv = begin match lv with
    | (Var _, _) -> lv
    | (Mem e, o) -> (Mem (strip_cast e), o) end in
  match exp with
  | Const _ -> exp
  | CastE(_, e) -> strip_cast e
  | UnOp(op, e, t) -> UnOp(op, strip_cast e, t)
  | BinOp(op, e1, e2, t) -> BinOp(op, strip_cast e1, strip_cast e2, t)
  | Lval lv -> Lval(strip_cast_lv lv)
  | AddrOf lv -> AddrOf(strip_cast_lv lv)
  | StartOf lv -> StartOf(strip_cast_lv lv)
  | _ -> E.s (E.bug "Not expected.")

(* If an expression contains unsupported operations (e.g., bit shifting), get
   a logStatement to be used in the if-stmt condition for generating
   an implication. For example, we get "b = 10 && c = 30" for "a = b & c"
   when the actual values for b and c are 10 and 30 respectively. *)
let rec unsupported_op_cond exp =
  let cond_e e = match e with Const _ -> ("", []) | _ ->
    let val_s, val_a = lossless_val e in
    (d_string "%a == " d_exp e) ^ val_s, val_a in
  let join_conds (s1, a1) (s2, a2) =
    let conj = if s1 = "" or s2 = "" then "" else " && " in
    if s2 = "" then s1, a1 else s1 ^ conj ^ s2, a1 @ a2 in
  match exp with
  | Const _ -> "", []
  | CastE(_, e) -> unsupported_op_cond e
  | UnOp(BNot, e, _) -> let s1, a1 = cond_e e in
                        let s2, a2 = unsupported_op_cond e in
                        join_conds (s1, a1) (s2, a2)
  | UnOp _ -> "", []
  | BinOp(op, e1, e2, _) -> begin match op with
    | Shiftlt | Shiftrt | BAnd | BXor | BOr ->
      let (s1, a1), (s2, a2) = cond_e e1, cond_e e2 in
      let (s3, a3), (s4, a4) = unsupported_op_cond e1, unsupported_op_cond e2 in
      List.fold_left join_conds ("", []) [s1, a1; s2, a2; s3, a3; s4, a4]
    | _ -> "", [] end
  | Lval lv | AddrOf lv | StartOf lv -> begin match lv with
    | (Var _, _) -> "", []
    | (Mem e, _) -> unsupported_op_cond e end
  | _ -> E.s (E.bug "Not expected.")

(* This function is for debugging only. *)
let rec has_str_lit = function
  | Const(CStr _) | Const(CWStr _) -> true
  | Const _ -> false
  | CastE(_, e) -> has_str_lit e
  | UnOp(_, e, _) -> has_str_lit e
  | BinOp(_, l, r,_) -> has_str_lit l || has_str_lit r
  | Lval lv | AddrOf lv | StartOf lv -> begin match lv with
    | (Var _, _) -> false | (Mem e, _) -> has_str_lit e end
  | _ -> E.s (E.bug "Not expected.")

let rec d_mem_exp ?pr_val (arg :exp) : logStatement =
  let pv = pr_val <> None in
  match arg with
  | Lval lv -> d_mem_lval ~pr_val:pv lv
  | Const(CStr s) -> to_c_string s, []
    (* TODO Bug: e.g., \031 in OCaml string is base 10.
    "\"%s\"", [mkString (String.escaped s)] *)
  | Const(CWStr s) -> E.s (E.bug "CWStr not supported.")
  | Const _ -> (d_string "%a" d_exp arg, [])
  | CastE(_, e) -> d_mem_exp ~pr_val:pv e
  | UnOp(o,e,_) ->
      let opStr = d_string "%a " d_unop o in
      let (str,arg) = d_mem_exp ~pr_val:pv e in
      (opStr ^"("^ str ^")", arg)

  | BinOp(op, e1, e2, t) -> begin match op with
    | IndexPI -> E.s (E.bug "IndexPI not expected.")
    | MinusPP -> E.s (E.bug "Let's see if MinusPP can appear.")
    | PlusPI | MinusPI ->
      let ut = unrollType t in
      (match ut with TPtr _ -> () | _ -> E.s (E.bug "Internal bug."));
      let sz_ptr = (bitsSizeOf ut) / 8 in
      let e2' = BinOp(Mult, e2, integer sz_ptr, t) in
      let op' = if op = PlusPI then PlusA else MinusA in
      d_mem_exp ~pr_val:pv (BinOp(op', e1, e2', t))
    | _ -> let e1_s, e1_a = d_mem_exp ~pr_val:pv e1 in
           let op_s = d_string " %a " d_binop op in
           let e2_s, e2_a = d_mem_exp ~pr_val:pv e2 in
           ("("^ e1_s ^")"^ op_s ^"("^ e2_s ^")", e1_a @ e2_a) end

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

(*
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
  | Set(lv, e, _) ->
    mkPrint (d_string "/* %a = %a; */\n" d_lval lv d_exp e) []
  | Call(lv_o, e, al, _) ->
    let rec arg_lst = function [] -> ""
      | [x] -> (d_string "%a" d_exp x)
      | x::xs -> (d_string "%a, " d_exp x) ^ arg_lst xs in
    let fn_name = d_string "%a" d_exp e in
    let lhs = match lv_o with None -> "(no return or ignored)"
                            | Some lv -> d_string "%a =" d_lval lv in
    mkPrint ("/* Call: "^ lhs ^" "^ fn_name ^"("^ (arg_lst al) ^"); */\n") []
  | _ -> E.s (E.bug "Invalid usage.")

(* Is this a string literal assignment? If yes, we need to assign an actual
   address directly. Don't worry about not making each individual character
   assignment though; memory variables affected by this entire string will be
   covered by 'postprocess_concrete.' *)
let is_str_lit_asgn = function
  | CastE(_, Const(CStr s)) | Const(CStr s) -> true
  | e -> if has_str_lit e then (* Checking if there can be other forms. *)
           E.s (E.bug "Unexpected assignemnt involving string literals.");
         false

class dsnconcreteVisitorClass = object
  inherit nopCilVisitor

  val mutable return_seen = false

  method vinst i = begin
    let print_orig = mk_print_orig i in (* For debugging info. *)
    match i with
      Set(lv, e, l) ->
        (* DSN Does anything go weird if we have function pointers *)
	let (lhs_s,lhs_a) = d_mem_lval lv in
        let (rhs_s,rhs_a) = d_mem_exp ~pr_val:true e in

        let if_s, if_a = unsupported_op_cond e in
        let pr_s1, pr_a1 = if if_s = "" then "", []
                                        else "if("^ if_s ^ "){ ", if_a in
        let pr_s1, pr_a1 = pr_s1 ^ lhs_s ^" = ", pr_a1 @ lhs_a in

        let val_s, val_a = lossless_val_lv lv in
        let special_cases =
          (rhs_s = "stdin" or rhs_s = "stdout" or rhs_s = "stderr") in
        let actual_val = (is_str_lit_asgn e) or (if_s <> "") or special_cases in

        (* Make it assign an actual value directly if needed. *)
        let pr_s2, pr_a2 = if actual_val then val_s, val_a
                                         else rhs_s, rhs_a in
        let pr_s2 = pr_s2 ^";"^ (if if_s <> "" then " }" else "") in

        (* For debugging, print the actual value assigned too. *)
        let pr_s2, pr_a2 = pr_s2 ^" /* Assigned: "^ val_s ^" */\n",
                           pr_a2 @ val_a in

        let print_asgn      = mkPrintNoLoc                pr_s1 pr_a1 in
        let print_asgn_post = mkPrintNoLoc ~noindent:true pr_s2 pr_a2 in
	let newInstrs =  [print_orig; print_asgn; i; print_asgn_post] in
	ChangeTo newInstrs

    (* The only calls that can occur in a reduced format are to functions
       where we do not have the implementation. *)
    | Call(lo,e,al,l) ->
        let lhs_s, lhs_a = match lo with None -> "", []
                                       | Some(lv) -> d_mem_lval lv in

	let printCalls = match lo with
	  | None -> [] (* No assignment; nothing to print. *)
	  | Some(lv) ->
              (* Print the actual return value stored in the left-hand side
                 variable in a lossless representation. *)
              let val_s, val_a = lossless_val_lv lv in
              [mkPrintNoLoc (lhs_s ^" = "^ val_s ^";\n") (lhs_a @ val_a)]
              (* Support for struct-copying returns disabled. Take a look at
                 'loosless_val' function.
              (* Declaring a tmp variable is a trick to use an initialization
                 form (e.g., { { 65, 66 }, 9 } for a struct). *)
              let typ_str = d_string "%a" d_type (typeOfLval lv) in
              [mkPrintNoLoc ("{ "^ typ_str ^" dsn_tmp_ret = "^ val_s ^";\n")
                            val_a;
               mkPrintNoLoc ("  "^ lhs_s ^" = dsn_tmp_ret; }\n") lhs_a] *) in
	ChangeTo (i :: print_orig :: printCalls)
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

let dsnconcrete (f: file) : unit =

  let globalDeclFn =
    let fdec = emptyFunction "__globalDeclFn" in
    let _ = setFunctionType fdec (TFun(voidType, Some[], false, [])) in
    fdec in

  let doGlobal (g: global) =

    let isFunc (v: varinfo) = match v.vtype with TFun _ -> true | _ -> false in

    let declareFn g =
      let var = match g with
        | GVarDecl(vi, _) -> vi.vname
        | GVar(vi, ii, _) -> begin match ii.init with
          | None -> vi.vname
          | Some (CompoundInit _) -> E.s (E.bug "Internal bug.")
          | Some (SingleInit e) ->
            (* TODO certain init values, e.g., 'stdin', should have taken
               an actual value assigned. However, it is complicated because
               static and global variables do not really observe the sequential
               init order. *)
            vi.vname ^" = "^ (d_string "%a" d_exp (strip_cast e)) end
        | _ -> E.s (E.bug "Internal bug.") in
      let str = "long long "^ var ^";\n" in
      globalDeclFn.sbody <-
        mkBlock (compactStmts [mkStmt (Block globalDeclFn.sbody);
                               mkStmtOneInstr (mkPrintNoLoc str [])]) in

    match g with
    | GVarDecl(vi, _) | GVar(vi, _, _) when isFunc vi ->
        (* If this surviving function requires a wrapper, change its name to
           point to the wrapper. Otherwise, don't bother printing anything. *)
        if SS.exists (fun x -> x = vi.vname) wrapper_fn_set
        then vi.vname <- vi.vname ^ wrapper_fn_postfix

    | GVarDecl(vi, _) when vi.vname = "optind"
                        || vi.vname = "optarg" -> declareFn g
    | GVar(vi, ii, _) -> begin match unrollType vi.vtype with
      (* For global arrays, structs and unions, force to assume that the address
         of the variable has been taken so that any elements or fields are
         accessed indirectly. We can then simply remove their declarations. 
         Initialization part will be covered by 'postprocess_concrete.' *)
      | TArray _ | TComp _ -> vi.vaddrof <- true
      | _ -> begin match ii.init with
        | Some (SingleInit e) -> begin match typeOf e with
          (* Same trick for string literal initialization. *)
          | TPtr(TInt(IChar, _), _) -> vi.vaddrof <- true
          | _ -> declareFn g end
        | _ -> declareFn g end
      end
    (* | GVarDecl _ | GType _ | GCompTag _ | GEnumTag _ *)

    | GFun (fdec, _) when fdec.svar.vname = "main" ->
        incrIndent ();
        let allVarDeclaresStmt = declareAllVarsStmt fdec.slocals in
        let _ = visitCilFunction dsnconcreteVisitor fdec in
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
