module S = SmtSimpleAst
module SB = SmtSimpleAstBuilder
module L =  SmtLibSyntax

let smtSimpleofSmtLib typeMap f = 
  let rec aux = function  
    | L.App (s,tl0,po) -> (
      let tl = List.map aux tl0 in
      match s with
      | L.BoolConst b -> SB.mk_boolConst b
      | L.IntConst i -> SB.mk_intConst i
      | L.Ident i ->
          begin
            match tl0 with
            | [L.App (L.IntConst n, _, _); L.App (L.IntConst m, _, _)] ->
                SB.mk_ident (Printf.sprintf "%s!%d!%d" i (Int64.to_int n) (Int64.to_int m)) (typeMap i)
            | _ -> SB.mk_ident i (typeMap i)
          end
      | L.Plus -> SB.mk_add tl
      | L.Mult -> SB.mk_mult tl
      | L.Minus -> SB.mk_minus tl
      | L.Div -> failwith "not handling div"
      | L.Eq -> SB.mk_app S.Eq tl
      | L.Gt ->  SB.mk_app S.Gt tl
      | L.Lt -> SB.mk_app S.Lt tl
      | L.Geq -> SB.mk_app S.Geq tl
      | L.Leq -> SB.mk_app S.Leq tl
      | L.Neq ->   SB.mk_app S.Neq tl   
      | L.And -> SB.mk_app S.And tl
      | L.Or -> SB.mk_app S.Or tl
      | L.Impl -> SB.mk_app S.Impl tl
      | L.Not -> SB.mk_app S.Not tl
      | L.Ite -> SB.mk_app S.Ite tl
    )
    | L.Binder _ -> failwith "not handeling binders"
    | L.Let _ -> failwith "not handeling lets"
    | L.Annot (t,a,po) -> aux t (* currently ignore annotations *)
  in
  aux (SmtLibSyntax.unletify f)

