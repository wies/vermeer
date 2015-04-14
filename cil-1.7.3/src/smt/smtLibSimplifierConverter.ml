module S = SmtSimpleAst
module L =  SmtLibSyntax

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
    | S.Mult -> L.Mult
    | S.Impl -> L.Impl
    | S.Ite -> L.Ite
  in 
  let relation_of_linearrelation op lhs rhs =
    let mults = List.map (fun (coeff,var) ->
      let vIdent = L.mk_const  (L.Ident var) in
      match coeff with
      | 0L -> failwith "shouldn't have 0 coefficients"
      | 1L -> vIdent
      | x -> L.mk_app L.Mult 
	[L.mk_const (L.IntConst (Int64.to_int x));
	 vIdent]
    ) lhs 
    in
    let newLhs = L.mk_app L.Plus mults in
    let newRhs = L.mk_const (L.IntConst (Int64.to_int rhs)) in
    L.mk_app (core_sym_of_simple_op op) [newLhs;newRhs]
  in
  let rec aux = function
    | S.BoolConst b -> L.mk_const (L.BoolConst b)
    | S.IntConst i -> L.mk_const (L.IntConst (Int64.to_int i))
    | S.Ident (v,s) -> L.mk_const (L.Ident v)
    | S.App (o,tl,s) -> L.mk_app (core_sym_of_simple_op o) (List.map aux tl)
    | S.LinearRelation (o,lhs,rhs) -> relation_of_linearrelation o lhs rhs
  in
  aux f
