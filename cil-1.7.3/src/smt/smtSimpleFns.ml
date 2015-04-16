open SmtSimpleAst

let get_idents formula  = 
  let rec aux set formula = 
    match formula with
    | BoolConst _ | IntConst _ -> set
    | Ident (v,s) -> VarSet.add v set
    | App (o,tl,s) -> List.fold_left aux set tl
    | LinearRelation(o,tl,v) ->  List.fold_left (fun set (c,v) -> VarSet.add v set) set tl
  in
  aux VarSet.empty formula


let string_of_term term = 
  let lib_term  = SmtLibSimplifierConverter.smtCore_of_smtSimple term in
  SmtLibSyntax.string_of_term lib_term

let assertion_of_formula name formula : SmtSimpleAst.assertion 
    = name,formula, get_idents formula

let string_of_assertion (name,formula,idents) = 
  "(assert (! " 
  ^ string_of_term formula
  ^ " :named " ^ name
  ^ "))\n"
