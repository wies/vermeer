open SmtSimpleAst

let string_of_term term = 
  let lib_term  = SmtLibSimplifierConverter.smtCore_of_smtSimple term in
  SmtLibSyntax.string_of_term lib_term
