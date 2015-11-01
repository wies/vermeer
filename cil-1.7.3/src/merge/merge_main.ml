open Xml

type statement_type = Assert | Assume | Assignment;;
type visibility = Global | Local of int;;
type variable_type = Int;;

type variable_declaration = {
  id : int;
  variable : int;
  ssa_index : int;
  var_type : variable_type;
  thread : visibility
};;

let variable_type_of_string var_type_str = 
  match var_type_str with
  | "int" -> Int
  | _ -> raise (Invalid_argument "Unsupported variable type")
;;

let string_of_variable_type var_type = 
  "int"
;;

let visibility_of_string vis_str = 
  match vis_str with
  | "global" -> Global
  | _ -> Local( (int_of_string vis_str) )
;;

let string_of_visibility vis_type = 
  match vis_type with
  | Global -> "global"
  | Local(x) -> string_of_int x
;;

let xml_format_of_variable_declaration vdecl = 
  "<variable-declaration id=\"" ^ (string_of_int vdecl.id) ^ "\" variable=\"" ^ (string_of_int vdecl.variable) ^ "\" ssa-index=\"" ^ (string_of_int vdecl.ssa_index) ^ "\" type=\"" ^ (string_of_variable_type vdecl.var_type) ^ "\" thread=\"" ^ (string_of_visibility vdecl.thread) ^ "\"/>"
;;

let variable_declaration_of_xml xml = 
{
  id = int_of_string (Xml.attrib xml "id");
  variable = int_of_string (Xml.attrib xml "variable");
  ssa_index = int_of_string (Xml.attrib xml "ssa-index");
  var_type = (variable_type_of_string (Xml.attrib xml "type"));
  thread = (visibility_of_string (Xml.attrib xml "thread"))
}
;;

let handle_variable_declarations xml =
  let aux decls xml_child = 
    decls @ [ (variable_declaration_of_xml xml_child) ]
  in
  let var_decls = Xml.fold aux [] xml in
  let aux_two element = print_endline (xml_format_of_variable_declaration element) in
  List.iter aux_two var_decls
;;


type expression_operator = EQ | NEQ | LT | GT | LEQ | GEQ;;

let expression_operator_of_string str = 
  match str with
  | "EQ" -> EQ
  | "NEQ" -> NEQ
  | "LT" -> LT
  | "LEQ" -> LEQ
  | "GT" -> GT
  | "GEQ" -> GEQ
  | _ -> raise (Invalid_argument "Unsupported operator")
;;

let string_of_expression_operator op =
  match op with
  | EQ -> "EQ"
  | NEQ -> "NEQ"
  | LT -> "LT"
  | LEQ -> "LEQ"
  | GT -> "GT"
  | GEQ -> "GEQ"
;;

type term = {
  variable_id : int;
  factor : int;
};;

let term_of_xml xml =
{
  variable_id = int_of_string (Xml.attrib xml "variable-id");
  factor = int_of_string (Xml.attrib xml "factor");
};;

let xml_format_of_term t = 
  "<term variable-id=\"" ^ (string_of_int t.variable_id) ^ "\" factor=\"" ^ (string_of_int t.factor) ^ "\"/>"
;;

type expression = {
  operator : expression_operator;
  constant : int;
  terms : term list;
};;

let xml_format_of_expression e = 
  let aux str term_element = 
    str ^ (xml_format_of_term term_element)
  in
  let str = List.fold_left aux "" e.terms in
  "<expression operator=\"" ^ (string_of_expression_operator e.operator) ^ "\" const=\"" ^ (string_of_int e.constant) ^ "\">\n" ^ str ^ "</expression>\n"
;;

type statement = {
  position : int;
  thread : int;
  stmt_type : statement_type
};;

let statement_type_of_string type_str = 
  match type_str with
  | "assignment" -> Assignment
  | "assert" -> Assert
  | "assume" -> Assume
  | _ -> raise (Invalid_argument "Not a valid statement type")
;;

let string_of_statement_type stmt_type = 
  match stmt_type with
  | Assignment -> "assignment"
  | Assert -> "assert"
  | Assume -> "assume"
;;

let xml_format_of_statement stmt = 
  "<statement position=\"" ^ (string_of_int stmt.position) ^ " thread=\"" ^ (string_of_int stmt.thread) ^ "\" type=\"" ^ (string_of_statement_type stmt.stmt_type) ^ "\"></statement>"
;;

let statement_of_xml xml = 
  { 
    position = int_of_string (Xml.attrib xml "position");
    thread = int_of_string (Xml.attrib xml "thread");
    stmt_type = statement_type_of_string (Xml.attrib xml "type")
  }
;;

let handle_statements xml = 
  let aux stmts xml_child =
    stmts @ [ (statement_of_xml xml_child) ]
  in
  let stmts = Xml.fold aux [] xml in
  let aux_two element = print_endline (xml_format_of_statement element) in
  List.iter aux_two stmts
;;


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
