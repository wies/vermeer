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

(* for future reference, how to add spaces in printf *)

(* we have a format string, and a list of expressions for the printf*)
type logStatement = string * exp list


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



let mkVarDecl (v : varinfo) : instr = 
  let(lhsStr,rhsStr) = mkTypeStr v.vtype in
  mkPrintNoLoc "%s %s__%d%s;\n" 
    [ mkString lhsStr; 
      mkString v.vname; 
      scopeLvalExpr;
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



let d_outerScope_exp (arg : exp) : logStatement =
  if (isLocalVarExp arg) then (d_string "%a__%%u" d_exp arg, [prevScopeExpr] )
  else (d_string "%a" d_exp arg,[])

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
(* DSN TODO - do I need to consider AddrOf and StartOF *)
(* DSN TODO - do I need to worry about special characters like %? *)
(* I think I can get away with not using brackets around everything.  But 
 * I can put them in to be sure if needed later *)
(* cil.ml does something weird     
 *  | SizeOfE (Lval (Var fv, NoOffset)) when fv.vname = 
 *  "__builtin_va_arg_pack" && (not !printCilAsIs) -> 
 *  text "__builtin_va_arg_pack()"
 *)
let rec d_scope_exp (arg :exp) : logStatement = 
   match arg with 
  | CastE(t,e) -> 
      let (str,arg) = d_scope_exp e in
      (d_string "(%a)(%s)" d_type t str,arg)
  | SizeOfE(e) -> 
      let (str,arg) = d_scope_exp e in
      (d_string "sizeof(%s) " str ,arg)
  | AlignOfE(e) ->
      let (str,arg) = d_scope_exp e in
      (d_string "__alignof__(%s)" str,arg)
  | UnOp(o,e,_) ->
      let opStr = d_string "%a " d_unop o in
      let (str,arg) = d_scope_exp e in
      (opStr ^ "(" ^ str ^ ")",arg)
  | BinOp(o,l,r,_) ->  
      let (lhsStr,lhsArg) = d_scope_exp l in
      let opStr = d_string " %a " d_binop o in
      let (rhsStr,rhsArg) = d_scope_exp r in
      ("(" ^ lhsStr ^ ")" ^ opStr ^ "(" ^ rhsStr ^ ")" ,lhsArg @ rhsArg)
  | AddrOf(l) -> let (lhsStr,lhsArg) = d_scope_lval l in
    ("&"^lhsStr, lhsArg)
  | StartOf(l) -> d_scope_lval l
  | _ -> 
      if (needsScopeId arg) then (d_string "%a__%%u" d_exp arg, [currentScopeExpr] )
      else (d_string "%a" d_exp arg,[])

	  
let mkReturnTemp : logStatement = ("__return__%u",[currentScopeExpr])

(* DSN perhaps there should be a common make print assgt function *)


let mkSaveReturn lo : instr list = 
  match lo with 
  | Some (lv) ->
      let (lhsStr,lhsArg) = d_outerScope_lval lv in
      let (rhsStr,rhsArg) = mkReturnTemp in
      let printStr = lhsStr ^  " = " ^ rhsStr ^ ";\n" in
      let printArgs = lhsArg @ rhsArg in
      let printCall = mkPrint printStr printArgs in
      [printCall]
  | None -> []


(*DSN have to handle function pointers *)
let getFunctionVinfo e = match e with 
| Lval(Var(vinfo),_) -> vinfo
|_ -> raise (Failure "Not even an Lval.  Did you use function pointers?")
      
let getFormals e : (string * typ * attributes) list = 
  let vinfo = getFunctionVinfo e in 
  match vinfo.vtype with 
  | TFun(rtyp,args,varargs,attr) -> argsToList args
  | _ -> raise (Failure "Not a function")
	

let mkArgAssgt  (argName,argType,argAttr) (actual : exp) = 
  let typeStr = d_string "%a " d_type argType in
  let lhsStr = argName ^ "__%u" in
  let lhsArgs = [currentScopeExpr] in
  let (rhsStr,rhsArgs) = d_outerScope_exp actual in
  let printStr = typeStr ^ lhsStr ^ " = " ^ rhsStr ^ ";\n" in
  let printArgs = lhsArgs @ rhsArgs in
  mkPrint printStr printArgs

let rec mkArgAssgtList 
    (formal : (string * typ * attributes) list) 
    (actual : exp list) 
    : instr list = 
  match formal,actual with 
  | [], [] -> []
  | (x::xs),(y::ys) ->  (mkArgAssgt x y)::(mkArgAssgtList xs ys)
  | _ -> raise (Failure "lists are different lengths")

(* DSN need a better name here *)
let rec mkActualArg (al : exp list) : logStatement = 
  match al with
  | [] -> ("",[])
  | x::[] -> d_scope_exp x
  | x::xs -> 
      let (thisStr,thisArg) = d_scope_exp x in
      let (restStr,restArgs) = mkActualArg xs in
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
  let vinfo = getFunctionVinfo e in
  match vinfo.vstorage with 
  | Extern -> false 
  | _ ->  not (Hashtbl.mem builtinFunctions vinfo.vname)

let i = ref 0
let name = ref ""


let makeScopeOpen = [ mkPrintNoLoc "{\n" []; 
		      incrScope		    
		    ]

let makeScopeClose = [decrScope; mkPrintNoLoc "}\n" []]


let currentFunc: string ref = ref ""

class dsnconcreteVisitorClass = object
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
	if (isDefinedFn e) then 
	  let formals = getFormals e in
	  let assgts = mkArgAssgtList formals al  in
	  let logFnName = [(mkPrint (d_string "//Calling %a\n" d_exp e)) []] in
	  let saveReturn = mkSaveReturn lo in 
	  let newInstrs =  
	    makeScopeOpen @ logFnName 
	    @ assgts @ [i] @ saveReturn @ makeScopeClose in 
	  ChangeTo newInstrs
	else
	  let (lhsStr,lhsArg) = 
	    match lo with
	    | Some(lv) -> let (s,a) = d_scope_lval lv in (s ^ " = ",a)
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
      Return(Some e, loc) -> 
        let pre = mkPrint (d_string "//exiting %s\n" !currentFunc) [] in
	let typeStr = d_string "%a " d_type (typeOf e) in
	let (lhsStr,lhsArg) = mkReturnTemp in
	let (rhsStr,rhsArg) = d_scope_exp e in
	let printStr = typeStr ^ lhsStr ^  " = " ^ rhsStr ^ ";\n" in
	let printArgs = lhsArg @ rhsArg in
	let printCall = mkPrint printStr printArgs in
	let printStmt = mkStmtOneInstr printCall in
	let preStmt = mkStmtOneInstr pre in
        ChangeTo (mkStmt (Block (mkBlock [ preStmt; printStmt ; s ])))
    | _ -> DoChildren

(* hiding this for now
(Some(e),l) ->
      let str = prefix ^ Pretty.sprint 800 ( Pretty.dprintf
        "Return(%%p) from %s\n" funstr ) in
      let newinst = ((Call (None, Lval(var printfFun.svar),
                                ( [ (* one ; *) mkString str ; e ]),
                                locUnknown)) : instr )in
      let new_stmt = mkStmtOneInstr newinst in
      let slist = [ new_stmt ; s ] in
      (ChangeTo(mkStmt(Block(mkBlock slist))))
    | Return(None,l) ->
      let str = prefix ^ (Pretty.sprint 800 ( Pretty.dprintf
        "Return void from %s\n" funstr)) in
      let newinst = ((Call (None, Lval(var printfFun.svar),
                                ( [ mkString str ]),
                                locUnknown)) : instr )in
      let new_stmt = mkStmtOneInstr newinst in
      let slist = [ new_stmt ; s ] in
      (ChangeTo(mkStmt(Block(mkBlock slist))))
    | _ -> DoChildren
*)
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
        ignore (visitCilFunction dsnVisitor fdec);
	
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
(*
	(* debugging 'anagram', it's really nice to be able to see the strings *)
	(* inside fat pointers, even if it's a bit of a hassle and a hack here *)
	let isFatCharPtr (cinfo:compinfo) =
	  cinfo.cname="wildp_char" ||
	  cinfo.cname="fseqp_char" ||
	  cinfo.cname="seqp_char" in

        (* Collect expressions that denote the actual arguments *)
        let actargs =
          (* make lvals out of args which pass test below *)
          (Util.list_map
            (fun vi -> match unrollType vi.vtype with
              | TComp(cinfo, _) when isFatCharPtr(cinfo) ->
                  (* access the _p field for these *)
                  (* luckily it's called "_p" in all three fat pointer variants *)
                  Lval(Var(vi), Field(getCompField cinfo "_p", NoOffset))
              | _ ->
                  Lval(var vi))

            (* decide which args to pass *)
            (List.filter
              (fun vi -> match unrollType vi.vtype with
                | TPtr(TInt(k, _), _) when isCharType(k) ->
                    !printPtrs || !printStrings
                | TComp(cinfo, _) when isFatCharPtr(cinfo) ->
                    !printStrings
                | TVoid _ | TComp _ -> false
                | TPtr _ | TArray _ | TFun _ -> !printPtrs
                | _ -> true)
              fdec.sformals)
          ) in

        (* make a format string for printing them *)
        (* sm: expanded width to 200 because I want one per line *)
        let formatstr = prefix ^ (Pretty.sprint 200
          (dprintf "entering %s(%a)\n" fdec.svar.vname
            (docList ~sep:(chr ',' ++ break)
              (fun vi -> match unrollType vi.vtype with
              | TInt _ | TEnum _ -> dprintf "%s = %%d" vi.vname
              | TFloat _ -> dprintf "%s = %%g" vi.vname
              | TVoid _ -> dprintf "%s = (void)" vi.vname
              | TComp(cinfo, _) -> (
                  if !printStrings && isFatCharPtr(cinfo) then
                    dprintf "%s = \"%%s\"" vi.vname
                  else
                    dprintf "%s = (comp)" vi.vname
                )
              | TPtr(TInt(k, _), _) when isCharType(k) -> (
                  if (!printStrings) then
                    dprintf "%s = \"%%s\"" vi.vname
                  else if (!printPtrs) then
                    dprintf "%s = %%p" vi.vname
                  else
                    dprintf "%s = (str)" vi.vname
                )
              | TPtr _ | TArray _ | TFun _ -> (
                  if (!printPtrs) then
                    dprintf "%s = %%p" vi.vname
                  else
                    dprintf "%s = (ptr)" vi.vname
                )
              | _ -> dprintf "%s = (?type?)" vi.vname))
            fdec.sformals)) in

        i := 0 ;
        name := fdec.svar.vname ;
        if !allInsts then (
          let thisVisitor = new verboseLogVisitor printfFun !name prefix in
          fdec.sbody <- visitCilBlock thisVisitor fdec.sbody
        );
        fdec.sbody.bstmts <-
              mkStmt (Instr [Call (None, Lval(var printfFun.svar),
                                ( (* one :: *) mkString formatstr 
                                   :: actargs),
                                loc)]) :: fdec.sbody.bstmts
 *)
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
  { fd_name = "dsncocrete";
    fd_enabled = Cilutil.dsnconcreteCalls;
    fd_description = "generation of code to log function calls";
    fd_extraopt = [];
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
