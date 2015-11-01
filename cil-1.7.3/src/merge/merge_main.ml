open Xml

(*type statement_type = Assert | Assume | Assignment;;*)
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
  "<term variable-id=\"" ^ (string_of_int t.variable_id) ^ "\" factor=\"" ^ (string_of_int t.factor) ^ "\"/>\n"
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

let expression_of_xml xml = 
  let op = expression_operator_of_string (Xml.attrib xml "operator") in
  let c = int_of_string (Xml.attrib xml "const") in
  let aux terms xml_child = (term_of_xml xml_child) :: terms in
  let ts = List.fold_left aux [] (Xml.children xml) in
  {
    operator = op;
    constant = c;
    terms = ts
  }
;;


type statement_info = {
  position : int;
  thread : int;
  guards : expression list
};;

type assignment_statement = {
  assigned_variable : int;
  constant : int;
  terms : term list
};;

type statement = Assertion of statement_info * expression | Assume of statement_info * expression | Assignment of statement_info * assignment_statement;;

let xml_format_of_statement stmt = 
  let position_str = 
    match stmt with
    | Assertion(stmt_info, _) -> string_of_int stmt_info.position
    | Assume(stmt_info, _) -> string_of_int stmt_info.position
    | Assignment(stmt_info, _) -> string_of_int stmt_info.position
  in
  let thread_str = 
    match stmt with
    | Assertion(stmt_info, _) -> string_of_int stmt_info.thread
    | Assume(stmt_info, _) -> string_of_int stmt_info.thread
    | Assignment(stmt_info, _) -> string_of_int stmt_info.thread
  in
  let type_str = 
    match stmt with
    | Assertion(_, _) -> "assert"
    | Assume(_, _) -> "assume"
    | Assignment(_, _) -> "assignment"
  in
  let guards_str = "" (* TODO implement *)
  in
  let stmt_str = 
    match stmt with
    | Assertion(_, expr) -> xml_format_of_expression expr
    | Assume(_, expr) -> xml_format_of_expression expr
    | Assignment(_, _) -> "" (* TODO implement *)
  in
  "<statement position=\"" ^ position_str ^ " thread=\"" ^ thread_str ^ "\" type=\"" ^ type_str ^ "\">\n" ^
  guards_str ^
  stmt_str ^
  "</statement>"
;;

let guards_of_xml xml = 
  (* iterate through children and keep guards *)
  let aux guards xml_child = 
    match (Xml.tag xml_child) with
    | "guard" -> let aux exprs xml_guard = (expression_of_xml xml_guard) :: exprs in List.fold_left aux [] (Xml.children xml_child)
    | _ -> guards
  in
  List.fold_left aux [] (Xml.children xml)
;;

let assertion_of_xml xml stmt_info = 
  let aux conditions xml_child = 
    (
      match (Xml.tag xml_child) with 
      | "expression" -> [ expression_of_xml xml_child ] 
      | _ -> conditions 
    )
  in 
  let c = List.hd (List.fold_left aux [] (Xml.children xml)) in 
  Assertion(stmt_info, c)
;;

let assume_of_xml xml stmt_info = 
  let aux conditions xml_child = 
    (
      match (Xml.tag xml_child) with 
      | "expression" -> [ expression_of_xml xml_child ] 
      | _ -> conditions 
    )
  in 
  let c = List.hd (List.fold_left aux [] (Xml.children xml)) in 
  Assume(stmt_info, c)
;;

let assignment_of_xml xml stmt_info = 
  let aux_lhs vars xml_child = 
    (
      match (Xml.tag xml_child) with 
      | "lhs" -> [ int_of_string (Xml.attrib xml_child "variable-id") ] 
      | _ -> vars 
    )
  in 
  let var_id = List.hd (List.fold_left aux_lhs [] (Xml.children xml)) in
  let aux_rhs_constant cs xml_child = 
    (
      match (Xml.tag xml_child) with
      | "rhs" -> [ int_of_string (Xml.attrib xml_child "const") ]
      | _ -> cs
    )
  in
  let c = List.hd (List.fold_left aux_rhs_constant [] (Xml.children xml)) in
  let aux_rhs_terms ts xml_child = 
    (
      match (Xml.tag xml_child) with
      | "rhs" -> 
        (
          let aux_terms ds xml_term = (term_of_xml xml_term) :: ds in
          List.fold_left aux_terms [] (Xml.children xml_child)
        )
      | _ -> ts
    )
  in
  let ts = List.fold_left aux_rhs_terms [] (Xml.children xml)  in
  Assignment(stmt_info, { assigned_variable = var_id; constant = c; terms = ts })
;;

let statement_of_xml xml = 
  let stmt_info = { 
    position = int_of_string (Xml.attrib xml "position");
    thread = int_of_string (Xml.attrib xml "thread");
    guards = guards_of_xml xml
  } in 
  match (Xml.attrib xml "type") with
  | "assert" -> assertion_of_xml xml stmt_info
  | "assume" -> assume_of_xml xml stmt_info
  | "assignment" -> assignment_of_xml xml stmt_info
  | _ -> raise (Invalid_argument "Unsupported statement type")
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
