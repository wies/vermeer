module S = Smtlib_ast
module L =  SmtLibSyntax

type t = Term of S.term | Formula of S.formula 

let smtSimple_of_smtCore =
  let convert_relation = function
    | L.Eq  -> S.EQ
    | L.Leq -> S.LEQ
    | L.Lt  -> S.LT
    | L.Geq -> S.GEQ
    | L.Gt  -> S.GT
    | L.Neq -> S.NEQ
    | _ -> failwith "bad op converstion"
  in
  let rec l_term_to_s_term = function
    | L.App (sym,tl,_) -> (
      let lst = List.map l_term_to_s_term tl in
      match sym with 
      | L.Ident v -> assert (tl = []); S.Variable v
      | L.Minus -> failwith "not supporting subtraction"
      | L.Plus -> S.Sum lst
      | L.Mult -> S.Mult lst
      | L.Div -> failwith "not supporting division"
      | _ -> failwith "cannot convert to simplifier term"
    )
    | _ -> failwith "cannot convert to simplifier term"
  and l_term_to_s_formula = function
    | L.App (sym,tl,_) -> (
      match sym with 
      | L.BoolConst true-> assert (tl = []); S.True
      | L.BoolConst false -> assert (tl = []); S.False
      | L.Ident v -> assert (tl = []); S.Boolvar v
      | L.Eq 
      | L.Gt 
      | L.Lt 
      | L.Geq 
      | L.Leq 
      | L.Neq ->
	(match tl with
	|[lhs;rhs] -> 
	  let op = convert_relation sym in
	  S.Relation(op,l_term_to_s_term lhs,l_term_to_s_term rhs)
	|_ -> failwith "can't convert relation")
      | L.And -> S.And (List.map l_term_to_s_formula tl)
      | L.Or -> S.Or (List.map l_term_to_s_formula tl)
      | L.Impl -> (match tl with 
	|[l;r] -> S.Implication (l_term_to_s_formula l,l_term_to_s_formula r) 
	| _ -> failwith "can't convert")
      | L.Not  -> (match tl with 
	|[l] -> S.Not (l_term_to_s_formula l )
	| _ -> failwith "can't convert")
      | L.Ite -> failwith "not yet"
      | L.IntConst _ | L.Minus | L.Plus | L.Mult | L.Div 
	-> failwith "cannot convert to simplifier formula"
    )
    | L.Binder _ -> failwith "not currently handeling quantifiers"
    | L.Let _ as t -> l_term_to_s_formula (L.unletify t)
    | L.Annot _ -> failwith "not converting annotations"
  in
()

let smtCore_of_smtSimple = 
  let convert_relation = function
    | S.EQ -> L.Eq
    | S.LEQ -> L.Leq
    | S.LT  -> L.Lt
    | S.GEQ -> L.Geq
    | S.GT -> L.Gt
    | S.NEQ -> L.Neq
  in
  let rec convert_term = function
    | S.Variable v -> L.mk_const (L.Ident v)
    | S.Value v -> L.mk_const (L.IntConst (*HACK*) (Int64.to_int v))
    | S.Sum tl -> L.mk_app L.Plus (List.map convert_term tl)
    | S.Mult tl -> L.mk_app L.Mult (List.map convert_term tl)
    | S.UnsupportedTerm s -> failwith ("cannot convert " ^ s)
  in
  let rec convert_formula = function
    | S.True -> L.mk_const (L.BoolConst true)
    | S.False -> L.mk_const (L.BoolConst false)
    | S.Not f -> L.mk_app L.Not [convert_formula f]
    | S.And fl -> L.mk_app L.And (List.map convert_formula fl)
    | S.Or fl ->  L.mk_app L.Or (List.map convert_formula fl)
    | S.Implication (f1,f2) ->  
      L.mk_app L.Impl [convert_formula f1; convert_formula f2]
    | S.Relation (op,lhs,rhs) -> 
      L.mk_app (convert_relation op) [convert_term lhs;convert_term rhs]
    | S.LinearRelation (op, lhs,rhs) -> 
      convert_formula (S.relation_of_linearrelation op lhs rhs)
    | S.ITE (f1,f2,f3) -> 
      L.mk_app L.Ite [convert_formula f1; convert_formula f2; convert_formula f3]
    | S.Boolvar v -> L.mk_const (L.Ident v)
    | S.UnsupportedFormula s -> failwith ("cannot convert " ^ s)
  in    
  convert_formula 
