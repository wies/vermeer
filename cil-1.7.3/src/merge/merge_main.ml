open Xml

type visibility = Global | Local of int;;
type variable_type = Int;;

type variable_declaration = {
  id : int;
  variable : int;
  ssa_index : int;
  var_type : variable_type;
  thread : visibility
};;

module VariableDeclarationMap = Map.Make(Int32);;

class variable_declaration_map =
  object(self)

    val mutable var_map = VariableDeclarationMap.empty

    method add vd = 
      var_map <- VariableDeclarationMap.add (Int32.of_int vd.id) vd var_map

    method add_all vds = 
      let aux vd = self#add vd in
      List.iter aux vds

    method get id = 
      VariableDeclarationMap.find (Int32.of_int id) var_map

    method print = 
      let aux key vd = print_endline (Int32.to_string key) in
      VariableDeclarationMap.iter aux var_map

  end;;


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
  "<variable-declaration id=\"" ^ (string_of_int vdecl.id) ^ "\" variable=\"" ^ (string_of_int vdecl.variable) ^ "\" ssa-index=\"" ^ (string_of_int vdecl.ssa_index) ^ "\" type=\"" ^ (string_of_variable_type vdecl.var_type) ^ "\" thread=\"" ^ (string_of_visibility vdecl.thread) ^ "\"/>\n"
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
  var_decls
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
    | Assertion(stmt_info, _) | Assume(stmt_info, _) | Assignment(stmt_info, _) -> string_of_int stmt_info.position
  in
  let thread_str = 
    match stmt with
    | Assertion(stmt_info, _) | Assume(stmt_info, _) | Assignment(stmt_info, _) -> string_of_int stmt_info.thread
  in
  let type_str = 
    match stmt with
    | Assertion(_, _) -> "assert"
    | Assume(_, _) -> "assume"
    | Assignment(_, _) -> "assignment"
  in
  let guards_str =     
    match stmt with
    | Assertion(stmt_info, _) | Assume(stmt_info, _) | Assignment(stmt_info, _) -> 
      let l = (List.length stmt_info.guards) in 
      let expr_str = 
        let aux s expr = s ^ (xml_format_of_expression expr) in
        List.fold_left aux "" stmt_info.guards
      in
      if (l > 0) then 
        "<guards size=\"" ^ (string_of_int l) ^ "\">\n" ^
        expr_str ^ 
        "</guards>\n" 
      else 
        ""
  in
  let stmt_str = 
    match stmt with
    | Assertion(_, expr) | Assume(_, expr) -> xml_format_of_expression expr
    | Assignment(_, astmt) -> 
      let aux_term s t = s ^ (xml_format_of_term t) in
      let term_str = List.fold_left aux_term "" astmt.terms in 
      "<lhs variable-id=\"" ^ (string_of_int astmt.assigned_variable) ^ "\"/>\n<rhs const=\"" ^ (string_of_int astmt.constant) ^ "\">\n" ^ term_str ^ "</rhs>\n"
  in
  "<statement position=\"" ^ position_str ^ "\" thread=\"" ^ thread_str ^ "\" type=\"" ^ type_str ^ "\">\n" ^
  guards_str ^
  stmt_str ^
  "</statement>\n"
;;

let guards_of_xml xml = 
  (* iterate through children and keep guards *)
  let aux guards xml_child = 
    match (Xml.tag xml_child) with
    | "guards" -> let aux exprs xml_guard = (expression_of_xml xml_guard) :: exprs in List.fold_left aux [] (Xml.children xml_child)
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
  stmts
;;


type trace = {
  nr_of_threads : int;
  variable_declarations : variable_declaration list;
  statements : statement list
};;

let xml_format_of_trace t = 
  let nr_of_decls = List.length t.variable_declarations in 
  let nr_of_stmts = List.length t.statements in 
  let aux_decls s decl = s ^ (xml_format_of_variable_declaration decl) in
  let decls_str = List.fold_left aux_decls "" t.variable_declarations in
  let aux_stmts s stmt = s ^ (xml_format_of_statement stmt) in
  let stmts_str = List.fold_left aux_stmts "" t.statements in
  "<trace nr-of-threads\"" ^ (string_of_int t.nr_of_threads) ^ "\">\n" ^
  "<declarations size=\"" ^ (string_of_int nr_of_decls) ^ "\">\n" ^
  decls_str ^
  "</declarations>\n" ^
  "<statements size=\"" ^ (string_of_int nr_of_stmts) ^ "\">\n" ^
  stmts_str ^
  "</statements>\n" ^
  "</trace>\n"
;;

let read_trace filename =
  (try
    let xml = Xml.parse_file filename in 
    if String.compare (Xml.tag xml) "trace" == 0 then
      let l = (Xml.children xml) in
      let aux_decls ds xml_child = 
        if String.compare (Xml.tag xml_child) "declarations" == 0 then
          (handle_variable_declarations xml_child) @ ds
        else 
          ds
      in
      let decls = List.fold_left aux_decls [] l in
      let aux_stmts ss xml_child = 
        if String.compare (Xml.tag xml_child) "statements" == 0 then
          (handle_statements xml_child) @ ss
        else 
          ss
      in
      let stmts = List.fold_left aux_stmts [] l in
      { nr_of_threads = (int_of_string (Xml.attrib xml "nr-of-threads")); variable_declarations = decls; statements = stmts }
    else
      raise (Invalid_argument "Malformed xml file!")
  with
    | Xml.Error msg -> raise (Failure "XML error: ...") (*Printf.printf "Xml error: %s\n" (Xml.error msg)*)
  )
;;

module ThreadMap = Map.Make(Int32)

let rec init_map i = 
  if i == 0 then
    let m = ThreadMap.empty in
    ThreadMap.add (Int32.of_int i) [] m
  else
    let m = init_map (i - 1) in
    ThreadMap.add (Int32.of_int i) [] m
;;

let decompose_trace trace = 
  let m = init_map (trace.nr_of_threads - 1) in
  let aux_stmts map stmt = 
    (
      let k = match stmt with | Assertion(si, _) | Assume(si, _) | Assignment(si, _) -> (Int32.of_int si.thread) in 
      let old_list = ThreadMap.find k map in 
      let new_list = old_list @ [ stmt ] in
      ThreadMap.add k new_list map
    ) in
  List.fold_left aux_stmts m trace.statements
;;

class set_of_traces = 
  object(self)
  
  val mutable set_of_sets_of_dataflows = []
  val mutable thread_local_executions = ThreadMap.empty

  method add = 1
  
  end
;;

let santas_little_aux vds = 
  let m = new variable_declaration_map in
  m#add_all vds;
  m#print
;;

let run () = 
  let trace = read_trace "example.xml" in
  print_endline (xml_format_of_trace trace);
  santas_little_aux trace.variable_declarations;
  let m = decompose_trace trace in
  let aux k v = 
    print_endline ((string_of_int (Int32.to_int k)) ^ " " ^ (string_of_int (List.length v))) in
  ThreadMap.iter aux m
;;
    
let () = run()

