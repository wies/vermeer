open SmtSimpleAst

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
