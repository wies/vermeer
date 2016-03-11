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
    let unapply_coefficient (coeff,var) = 
      let vIdent = L.mk_const (L.Ident var) in
      match coeff with
      | 0L -> failwith "shouldn't have 0 coefficients"
      | 1L -> vIdent
      | x -> L.mk_app L.Mult 
	[L.mk_const (L.IntConst x);
	 vIdent]
    in
    let newLhs = (match lhs with
      | [] -> failwith "bad lhs"
      | [(c,v) as coeff] -> unapply_coefficient coeff
      | _ ->  L.mk_app L.Plus (List.map unapply_coefficient lhs)
    ) in
    let newRhs = L.mk_const (L.IntConst rhs) in
    L.mk_app (core_sym_of_simple_op op) [newLhs;newRhs]
  in
  let rec aux = function
    | S.BoolConst b -> L.mk_const (L.BoolConst b)
    | S.IntConst i -> L.mk_const (L.IntConst i)
    | S.Ident (v,s) ->
        let regexp = Str.regexp "\\(rd\\|wr\\)!\\([0-9]*\\)!\\([0-9]*\\)" in
        if Str.string_match regexp v 0 
        then
          let w = Str.matched_group 1 v in
          let n = Int64.of_string (Str.matched_group 2 v) in
          let m = Int64.of_string (Str.matched_group 3 v) in
          L.mk_app (L.Ident w) [L.mk_const (L.IntConst n); L.mk_const (L.IntConst m)]
        else 
        L.mk_const (L.Ident v)
    | S.App (o,tl,s) -> L.mk_app (core_sym_of_simple_op o) (List.map aux tl)
    | S.LinearRelation (o,lhs,rhs) -> relation_of_linearrelation o lhs rhs
  in
  aux f
