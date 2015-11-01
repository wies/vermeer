open Xml

let handle_variable_declarations xml =
  let aux decls xml_child = (Xml.attrib xml_child "id") :: decls in
  let var_decls = List.rev (Xml.fold aux [] xml) in
  let aux_two element = print_endline element in
  List.iter aux_two var_decls

let handle_statements xml = 
  print_endline "TODO: handle_statements"

let rec process_trace_children l = 
  match l with 
  | x :: m -> 
    process_trace_children m;
    (
      match (Xml.tag x) with
      | "declarations" -> handle_variable_declarations x
      | "statements" -> handle_statements x
      | _ -> ()
    )
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
