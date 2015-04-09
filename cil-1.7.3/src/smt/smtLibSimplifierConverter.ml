module S = SmtSimpleAst
module L =  SmtLibSyntax

let core_sym_of_simple_op = function
  | S.Eq -> L.Eq
  | S.Leq -> L.Leq
  | S.Lt  -> L.Lt
  | S.Geq -> L.Geq
  | S.Gt ->L.Gt
  | S.Neq -> L.Neq
  | S.And -> L.And
  | S.Or -> L.Or
  | S.Not -> L.Not
  | S.Add  -> L.Plus
  | S.Mult -> L.Minus
  | S.Impl -> L.Impl
  | S.Ite -> L.Ite

let smtCore_of_smtSimple f = 
  let core_sym_of_simple_op = function
  | S.Eq -> L.Eq
  | S.Leq -> L.Leq
  | S.Lt  -> L.Lt
  | S.Geq -> L.Geq
  | S.Gt ->L.Gt
  | S.Neq -> L.Neq
  | S.And -> L.And
  | S.Or -> L.Or
  | S.Not -> L.Not
  | S.Add  -> L.Plus
  | S.Mult -> L.Minus
  | S.Impl -> L.Impl
  | S.Ite -> L.Ite
  in 
  let rec aux = function
    | S.BoolConst b -> L.mk_const (L.BoolConst b)
    | S.IntConst i -> L.mk_const (L.IntConst (Int64.to_int i))
    | S.Ident (v,s) -> L.mk_const (L.Ident v)
    | S.App (o,tl,s) -> L.mk_app (core_sym_of_simple_op o) (List.map aux tl)
    | S.LinearRelation (o,lhs,rhs) -> aux (S.relation_of_linearrelation o lhs rhs)
  in
  aux f

let smtSimpleofSmtLib typeMap f = 
  let rec aux = function  
    | L.App (s,tl,po) -> (
      let tl = List.map aux tl in
      match s with
      | L.BoolConst b -> S.mk_boolConst b
      | L.IntConst i -> S.mk_intConst (Int64.of_int i)
      | L.Ident i -> S.mk_ident i (typeMap i)
      | L.Plus -> S.mk_add tl
      | L.Mult -> S.mk_mult tl
      | L.Div | L.Minus -> failwith "not handling div and mult"
      | L.Eq -> S.mk_app S.Eq tl
      | L.Gt ->  S.mk_app S.Gt tl
      | L.Lt -> S.mk_app S.Lt tl
      | L.Geq -> S.mk_app S.Geq tl
      | L.Leq -> S.mk_app S.Leq tl
      | L.Neq ->   S.mk_app S.Neq tl   
      | L.And -> S.mk_app S.And tl
      | L.Or -> S.mk_app S.Or tl
      | L.Impl -> S.mk_app S.Impl tl
      | L.Not -> S.mk_app S.Not tl
      | L.Ite -> S.mk_app S.Ite tl
    )
    | L.Binder _ -> failwith "not handeling binders"
    | L.Let _ -> failwith "not handeling lets"
    | L.Annot (t,a,po) -> aux t (* currently ignore annotations *)
  in
  aux (SmtLibSyntax.unletify f)

