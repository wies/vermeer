open Xml

type variable_declaration = {
  id : int;
  variable : int;
  ssa_index : int;
  variable_type : string;
  thread : string
};;

let xml_format_of_variable_declaration vdecl = 
  "<variable-declaration id=\"" ^ (string_of_int vdecl.id) ^ "\" variable=\"" ^ (string_of_int vdecl.variable) ^ "\" ssa-index=\"" ^ (string_of_int vdecl.ssa_index) ^ "\" type=\"" ^ vdecl.variable_type ^ "\" thread=\"" ^ vdecl.thread ^ "\"/>";;

let handle_variable_declarations xml =
  let aux decls xml_child = 
    decls @ [ {
      id = int_of_string (Xml.attrib xml_child "id");
      variable = int_of_string (Xml.attrib xml_child "variable");
      ssa_index = int_of_string (Xml.attrib xml_child "ssa-index");
      variable_type = (Xml.attrib xml_child "type");
      thread = (Xml.attrib xml_child "thread")
    } ]
  in
  let var_decls = Xml.fold aux [] xml in
  let aux_two element = print_endline (xml_format_of_variable_declaration element) in
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
