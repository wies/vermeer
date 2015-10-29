open Xml

let handle_variable_declarations xml =
  print_endline "TODO: handle_variable_declarations"

let handle_statements xml = 
  print_endline "TODO: handle_statements"

let rec process_trace_children l = 
  match l with 
  | x :: m -> print_endline (Xml.tag x); process_trace_children m
  | [] -> ()

let handle_trace xml = 
  if String.compare (Xml.tag xml) "trace" == 0 then
    process_trace_children (Xml.children xml)
  else
    print_endline "ERROR: malformed xml file!"

let run () = 
  (try
    let x = Xml.parse_file "example.xml" (*(Xml.parse_string "<bla>hello</bla>")*)
    in 
      handle_trace x
  with
    | Xml.Error msg -> Printf.printf "Xml error: %s\n" (Xml.error msg)
  )
    
let () = run()
