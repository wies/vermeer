(** See copyright notice at the end of this file *)
(* DSN todo rename lhsStr to ((preTypeStr,preTypeArgs),(postTypeStr,postTypeArgs)) *)
(* TODO print globals before main *)
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

(* for future reference, how to add spaces in printf *)

(* we have a format string, and a list of expressions for the printf*)
type logStatement = string * exp list

let argTempBasename = "__arg_tmp_"
let commentLine = "//"

let scopeVar = makeGlobalVar "__scope_level__" Cil.uintType
let scopeLval =  (Var(scopeVar),NoOffset)
let scopeLvalExpr = Lval(scopeLval)
let currentScopeExpr = scopeLvalExpr
let currentIndentExpr = BinOp(Mult,currentScopeExpr,Cil.integer(indentSpaces),Cil.uintType)
let prevScopeExpr = BinOp(MinusA,currentScopeExpr,one,Cil.uintType)

let incrScope = Set(scopeLval, (increm scopeLvalExpr (1)), locUnknown)
let decrScope = Set(scopeLval, (increm scopeLvalExpr (-1)), locUnknown)

(* Switches *)
let printFunctionName = ref "printf"

let addProto = ref false

let d_string (fmt : ('a,unit,doc,string) format4) : 'a = 
  let f (d: doc) : string = 
    Pretty.sprint 800 d
  in
  Pretty.gprintf f fmt 

let d_tempArg (idx : int) : logStatement = 
  (argTempBasename ^ string_of_int idx ^ "__%u ",[currentScopeExpr])

let lineStr (loc: location) : string = 
  "#line " ^ string_of_int loc.line ^ " \"" ^ loc.file ^ "\"" 
    

let printf: varinfo option ref = ref None
let makePrintfFunction () : varinfo = 
    match !printf with 
      Some v -> v
    | None -> begin 
        let v = makeGlobalVar !printFunctionName 
                     (TFun(intType, Some [("format", charConstPtrType, [])],
                             true, [])) in
        printf := Some v;
        addProto := true;
        v
    end


let mkPrintNoLoc (format: string) (args: exp list) : instr = 
  let p: varinfo = makePrintfFunction () in 
  let format = if printIndent then  "%*s" ^ format else format in
  let args = if printIndent then currentIndentExpr :: mkString "" :: args 
  else args in  
  Call(None, Lval(var p), (mkString format) :: args, !currentLoc)

let mkPrint (format: string) (args: exp list) : instr = 
  let p: varinfo = makePrintfFunction () in 
  let format = if printIndent then  "%*s" ^ format else format in
  let format = "%s\n" ^ format in
  let locArg = mkString (lineStr !currentLoc)  in
  let args = if printIndent then currentIndentExpr :: mkString "" :: args 
  else args in  
  let args = locArg :: args in
  Call(None, Lval(var p), (mkString format) :: args, !currentLoc)

let mkPrintNoIdent (format: string) (args: exp list) : instr = 
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
| Lval(l) -> isLocalVarLval l
| AddrOf(l) -> isLocalVarLval l
| StartOf(l) -> isLocalVarLval l
| _ -> false

let needsScopeId (e: exp) = isLocalVarExp e

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
  ((lhsStr ^ " %s__%d" ^ rhsStr),
   (lhsArgs @ [ mkString v.vname; currentScopeExpr] @ rhsArgs))
    
let mkVarDecl (v : varinfo) : instr = 
  let (str,args) = d_decl v in
  mkPrintNoLoc (str ^ ";\n") args
   
let rec declareAllVarsHelper (slocals : varinfo list) : instr list = 
  match slocals with
  | x :: xs -> (mkVarDecl x) :: (declareAllVarsHelper xs)
  | [] -> []

let declareAllVarsStmt (slocals : varinfo list) : stmt list =
  let instrs = declareAllVarsHelper slocals in
  let stmts = List.map (fun x -> mkStmtOneInstr x) instrs in
  compactStmts stmts


let mkFormalDecl (v : varinfo) (idx : int) : instr = 
  let (lhsStr,lhsArgs) = d_decl v in
  let (rhsStr, rhsArgs) = d_tempArg idx in
  let argStr = lhsStr ^ " = " ^ rhsStr ^ ";\n" in
  mkPrintNoLoc argStr ( lhsArgs @ rhsArgs)   
  
let rec declareAllFormalsHelper (slocals : varinfo list) (idx : int) : instr list = 
  match slocals with
  | x :: xs -> (mkFormalDecl x idx ) :: (declareAllFormalsHelper xs (idx + 1))
  | [] -> []


let declareAllFormalsStmt (sformals : varinfo list) : stmt list = 
  let instrs = declareAllFormalsHelper sformals 0 in
  let stmts = List.map (fun x -> mkStmtOneInstr x) instrs in
  compactStmts stmts


(* two ways we might need a current scope expression here
 * the first is that we are directly a variable
 * the second is that it is a memory access
 *)
let d_scope_lval (arg : lval) : logStatement = 
  if (isLocalVarLval arg) then (d_string "%a__%%u" d_lval arg, [currentScopeExpr] )
  else (d_string "%a" d_lval arg,[])

let d_outerScope_lval (arg : lval) : logStatement = 
  if (isLocalVarLval arg) then (d_string "%a__%%u" d_lval arg, [prevScopeExpr] )
  else (d_string "%a" d_lval arg,[])


(* print an expression *)
(* DSN TODO - do I need to worry about special characters like %? *)
(* I think I can get away with not using brackets around everything.  But 
 * I can put them in to be sure if needed later *)
(* cil.ml does something weird     
 *  | SizeOfE (Lval (Var fv, NoOffset)) when fv.vname = 
 *  "__builtin_va_arg_pack" && (not !printCilAsIs) -> 
 *  text "__builtin_va_arg_pack()"
 *)
let d_xScope_exp  (scopeExp : exp)  = 
  let rec dExp (arg :exp) : logStatement = 
   match arg with 
   | Const(CStr(s)) -> ("\"%s\"",[mkString s])
   | CastE(t,e) -> 
       let (str,arg) = dExp e in
       (d_string "(%a)(%s)" d_type t str,arg)
   | SizeOfE(e) -> 
       let (str,arg) = dExp e in
       (d_string "sizeof(%s) " str ,arg)
   | AlignOfE(e) ->
       let (str,arg) = dExp e in
       (d_string "__alignof__(%s)" str,arg)
   | UnOp(o,e,_) ->
       let opArg = mkString (d_string "%a" d_unop o) in
       let (str,arg) = dExp e in
       ("%s(" ^ str ^ ")",[opArg] @ arg)
   | BinOp(o,l,r,_) ->  
       let (lhsStr,lhsArg) = dExp l in
       let opArg = mkString (d_string "%a" d_binop o) in
       let (rhsStr,rhsArg) = dExp r in
       ("(" ^ lhsStr ^ ") %s (" ^ rhsStr ^ ")" ,lhsArg @ [opArg] @ rhsArg)
   | AddrOf(l) -> let (lhsStr,lhsArg) = d_scope_lval l in
     ("&"^lhsStr, lhsArg)
   | StartOf(l) -> d_scope_lval l
   | _ -> 
       if (needsScopeId arg) then (d_string "%a__%%u" d_exp arg, [scopeExp] )
       else (d_string "%a" d_exp arg,[])
  in dExp
    
let d_outerScope_exp = d_xScope_exp prevScopeExpr
let d_scope_exp = d_xScope_exp currentScopeExpr
	  
let d_returnTemp : logStatement = ("__return__%u",[currentScopeExpr])

(* DSN perhaps there should be a common make print assgt function *)
let mkCopyReturnToOuterscope lo : instr list = 
  match lo with 
  | Some (lv) ->
      let (lhsStr,lhsArg) = d_outerScope_lval lv in
      let (rhsStr,rhsArg) = d_returnTemp in
      let printStr = lhsStr ^  " = " ^ rhsStr ^ ";\n" in
      let printArgs = lhsArg @ rhsArg in
      let printCall = mkPrint printStr printArgs in
      [printCall]
  | None -> []

let mkReturnTemp lo : instr list = 
  match lo with 
    | Some (lv) ->
	let ((lhsStr,lhsArgs),(rhsStr,rhsArgs)) = d_logType (typeOfLval lv) in 
	let (varNameStr,varNameArgs) = d_returnTemp in
       	let printStr = lhsStr ^ varNameStr ^ rhsStr ^ ";\n" in
	let printArgs  = lhsArgs @ varNameArgs @ rhsArgs in
	let printCall = mkPrint printStr printArgs in
	[printCall]
    | None -> []

(*DSN have to handle function pointers *)
let getFunctionVinfo e = match e with 
| Lval(Var(vinfo),_) -> vinfo
|_ -> raise (Failure ("Not even an Lval.  Did you use function pointers?\n" ^ 
		      Printexc.raw_backtrace_to_string (Printexc.get_callstack 100) ^ 
		      sprint 800 (d_thisloc ())))
      
(* DSN currently this only works for expressions that are 
 * directly functions.  Does not work for function ptrs 
 *)
let getFormals e : (string * typ * attributes) list = 
  let vinfo = getFunctionVinfo e in 
  match vinfo.vtype with 
  | TFun(rtyp,args,varargs,attr) -> argsToList args
  | _ -> raise (Failure ("Not a function.\n" ^
			 sprint 800 (d_thisloc ())))

let mkActualToTemp (actual : exp) (idx : int) = 
  let ((preTypeStr,preTypeArgs),(postTypeStr,postTypeArgs)) = d_logType (typeOf actual) in 
  let (lhsStr,lhsArgs) = d_tempArg idx in
  let (rhsStr,rhsArgs) =  d_outerScope_exp actual in
  let printStr = preTypeStr ^ " " ^ lhsStr ^ postTypeStr ^ " = " ^ rhsStr ^ ";\n" in
  let printArgs = 
    preTypeArgs 
    @ lhsArgs 
    @ postTypeArgs
    @ rhsArgs in
  mkPrint printStr printArgs

let rec mkActualsToTempsRec (actual : exp list) (idx : int) : instr list  = 
  match actual with 
  | [] -> []
  | x :: xs -> (mkActualToTemp x idx) :: (mkActualsToTempsRec xs (idx +1))

let mkActualsToTempInstrs (actual :exp list) : instr list = 
  mkActualsToTempsRec actual 0

let mkTempToFormal (formal : (string * typ * attributes)) (idx : int) = 
  let (formalName,formalType,formalAttr) = formal in
  let ((preTypeStr,preTypeArgs),(postTypeStr,postTypeArgs)) = d_logType formalType in 
  let lhsStr = formalName ^ "__%u" in
  let lhsArgs = [currentScopeExpr] in
  let (rhsStr,rhsArgs) = d_tempArg idx in
  let printStr = preTypeStr ^ " " ^ lhsStr ^ postTypeStr ^ " = " ^ rhsStr ^ ";\n" in
  let printArgs = 
    preTypeArgs 
    @ lhsArgs 
    @ postTypeArgs
    @ rhsArgs in
  mkPrint printStr printArgs

let rec mkTempToFormalListRec  (formals : (string * typ * attributes) list) (idx : int) : instr list  = 
  match formals with 
  | [] -> []
  | x :: xs -> (mkTempToFormal x idx) :: (mkTempToFormalListRec xs (idx +1))

let mkTempToFormalList (formals : (string * typ * attributes) list) : instr list = 
  mkTempToFormalListRec formals 0



(* DSN need a better name here *)
let rec mkConcreteArgs (al : exp list) : logStatement = 
  match al with
  | [] -> ("",[])
  | x::[] -> d_scope_exp x
  | x::xs -> 
      let (thisStr,thisArg) = d_scope_exp x in
      let (restStr,restArgs) = mkConcreteArgs xs in
      (thisStr ^ ", " ^ restStr, thisArg @ restArgs)



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


let isDefinedFn e =
  true
(*
  let vinfo = getFunctionVinfo e in
  match vinfo.vstorage with 
  | Extern -> false 
  | _ ->  not (Hashtbl.mem builtinFunctions vinfo.vname)
*)
let i = ref 0
let name = ref ""


let makeScopeOpen = [ mkPrintNoLoc "{\n" []; 
		      incrScope		    
		    ]

let makeScopeClose = [decrScope; mkPrintNoLoc "}\n" []]


let currentFunc: string ref = ref ""

class dsnVisitorClass = object
  inherit nopCilVisitor

  val printfFun =   
    let fdec = emptyFunction "printf" in
    fdec.svar.vtype <- TFun(intType, 
                            Some [
                                   ("format", charConstPtrType, []) ], 
                            true, []);
    fdec

  (* Watch for a declaration for our printer *)
  
  method vinst i = begin
    match i with
      Set(lv, e, l) -> 
	let (lhsStr,lhsArg) = d_scope_lval lv in
(* assume that we only have reduced expressions at this point!  Should maybe put an assert
   of that here? *)
(* DSN Does anything go weird if we have function pointers *)
	let (rhsStr,rhsArg) = d_scope_exp e in
	let printStr = lhsStr ^  " = " ^ rhsStr ^ ";\n" in
	let printArgs = lhsArg @ rhsArg in
	let printCall = mkPrint printStr printArgs in
	let newInstrs =  printCall :: [i] in
	ChangeTo newInstrs
    | Call(lo,e,al,l) ->
(* first, make the actual call.  If we know we can log the 
   * internals, print this as a comment *)
	let (lhsStr,lhsArg) = 
	  match lo with
	  | Some(lv) -> let (s,a) = d_scope_lval lv in (s ^ " = ",a)
	  | None -> ("",[])
	in
	let fnName = d_string "%a" d_exp e in
	let (argsStr, argsArgs) = mkConcreteArgs al in
	let callStr = lhsStr ^ fnName ^ "(" ^ argsStr ^ ");\n" in
	let callStr = if (isDefinedFn e) then  commentLine ^ callStr else callStr in
	let callArgs = lhsArg @ argsArgs in
	let logCall = [mkPrint callStr callArgs] in
(* Now, we are ready to log the variables into temps.  In some cases, we might not need
   * to actually use them *)
	let temps = mkActualsToTempInstrs al in
	let returnTemp = mkReturnTemp lo in
	let saveReturn = mkCopyReturnToOuterscope lo in 
	let newInstrs =  
	  makeScopeOpen @ logCall 
	  @ temps @ returnTemp 
	  @ [i] 
	  @ saveReturn @ makeScopeClose in 
	  ChangeTo newInstrs
    | _ -> DoChildren
  end
  method vstmt (s : stmt) = begin
    match s.skind with
      Return(Some e, loc) -> 
        let pre = mkPrint (d_string "//exiting %s\n" !currentFunc) [] in
	let (lhsStr,lhsArg) = d_returnTemp in
	let (rhsStr,rhsArg) = d_scope_exp e in
	let printStr = lhsStr ^  " = " ^ rhsStr ^ ";\n" in
	let printArgs = lhsArg @ rhsArg in
	let printCall = mkPrint printStr printArgs in
	let printStmt = mkStmtOneInstr printCall in
	let preStmt = mkStmtOneInstr pre in
        ChangeTo (mkStmt (Block (mkBlock [ preStmt; printStmt ; s ])))
    | _ -> DoChildren
  end
end

let dsnVisitor = new dsnVisitorClass


let dsn (f: file) : unit =

  let doGlobal = function
      
    | GVarDecl (v, _) when v.vname = !printFunctionName -> 
        if !printf = None then
          printf := Some v 
    | GFun (fdec, loc) ->
        currentFunc := fdec.svar.vname;
        (* do the body *)
        ignore (visitCilFunction dsnVisitor fdec);
	
        (* Now add the entry instruction *)
        if !currentFunc = "main" then 
	  let formalDeclList = List.map d_decl fdec.sformals in
	  let rec mkMainArgs lst = 
	    match lst with 
	    | x :: [] -> x
	    | x :: xs -> 
		let (strs,args) = mkMainArgs xs in
		let (str,arg) = x in
		(str ^ ", " ^ strs, arg @ args)
	    | _ -> raise (Failure ("main with no args???\n" ^ 
				   sprint 800 (d_thisloc ()))) in 
	  let (formalStr, formalArgs) = mkMainArgs formalDeclList in
	  fdec.sbody <- 
            mkBlock (compactStmts (
		     [mkStmtOneInstr (mkPrintNoIdent ("int main(" 
				      ^ formalStr 
				      ^ "){\n") formalArgs)]
		     @ [ mkStmtOneInstr (incrScope)] 
                     (* DSN need to add code to declare argc argv *)
		     @ (declareAllVarsStmt fdec.slocals) 
		     @ [mkStmt (Block fdec.sbody) ]
			 ))
       	else 
	  fdec.sbody <- 
            mkBlock (compactStmts (
		     [mkStmtOneInstr (mkPrint (d_string "//enter %s\n" !currentFunc) [])]
		     @ (declareAllFormalsStmt fdec.sformals) 
		     @ (declareAllVarsStmt fdec.slocals) 
		     @ [mkStmt (Block fdec.sbody) ]
			 ))	
    | _ -> ()
  in
  Stats.time "dsn" (iterGlobals f) doGlobal;
  if !addProto then begin
    let p = makePrintfFunction () in 
    E.log "Adding prototype for call logging function %s\n" p.vname;
    f.globals <- 
      GVarDecl (p, locUnknown) ::
      GVarDecl (scopeVar, locUnknown) :: 
      f.globals
  end  

let feature : featureDescr = 
  { fd_name = "dsn";
    fd_enabled = Cilutil.dsnCalls;
    fd_description = "generation of code to log function calls";
    fd_extraopt = [
      ("--dsnprintf", Arg.String (fun s -> printFunctionName := s), 
       " the name of the printf function to use");
      ("--dsnaddproto", Arg.Unit (fun s -> addProto := true), 
       " whether to add the prototype for the printf function")
    ];
    fd_doit = dsn;
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
