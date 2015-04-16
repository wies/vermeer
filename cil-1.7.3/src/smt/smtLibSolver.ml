(** SMT-LIB v2 solver interface *)

let read_from_chan chan =
  let lexbuf = Lexing.from_channel chan in
  (* This is useful for debugging, but not necessary *)
  (*SmtLibLexer.set_file_name lexbuf session.log_file_name; *)
  SmtLibParser.output SmtLibLexer.token lexbuf
