#include "xml.h"

#include <cstdlib>
#include <cstring>
#include <string>
#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>

#include "rapidxml-1.13/rapidxml.hpp"

#include "error.h"
#include "trace.h"

std::ostream& operator<<(std::ostream& out, const exe::variable_declaration_t& vd) {
  std::string thread_str;
  if (vd.thread < 0) {
    thread_str = "global";
  }
  else {
    thread_str = '0' + vd.thread;
  }

  out << "<variable-declaration "
      << "id=\"" << vd.id << "\" "
      << "variable=\"" << vd.variable << "\" "
      << "ssa-index=\"" << vd.ssa_index << "\" "
      << "type=\"int\" "
      << "thread=\"" << thread_str << "\"/>";

  return out;
}

void print2xml(std::ostream& out, const expr::linear_product_t<int>& p) {
  out << "<term variable-id=\"" << p.variable << "\" factor=\"" << p.factor << "\"/>";
}

expr::expr_t<int>::ops str2ops(const char* str) {
  expr::expr_t<int>::ops o;

  if (strcmp(str, "EQ") == 0) {
    o = expr::expr_t<int>::EQ;
  }
  else if (strcmp(str, "NEQ") == 0) {
    o = expr::expr_t<int>::NEQ;
  }
  else if (strcmp(str, "LT") == 0) {
    o = expr::expr_t<int>::LT;
  }
  else if (strcmp(str, "LEQ") == 0) {
    o = expr::expr_t<int>::LEQ;
  }
  else if (strcmp(str, "GT") == 0) {
    o = expr::expr_t<int>::GT;
  }
  else if (strcmp(str, "GEQ") == 0) {
    o = expr::expr_t<int>::GEQ;
  }
  else {
    ERROR("Unrecognized expression operator!");
  }

  return o;
}

std::string ops2str(expr::expr_t<int>::ops o) {
  std::string s;

  switch (o) {
    case expr::expr_t<int>::EQ:
      s = "EQ";
      break;
    case expr::expr_t<int>::NEQ:
      s = "NEQ";
      break;
    case expr::expr_t<int>::LT:
      s = "LT";
      break;
    case expr::expr_t<int>::LEQ:
      s = "LEQ";
      break;
    case expr::expr_t<int>::GT:
      s = "GT";
      break;
    case expr::expr_t<int>::GEQ:
      s = "GEQ";
      break;
    default:
      ERROR("Unrecognized operator!");
  }

  return s;
}

void print2xml(std::ostream& out, const expr::expr_t<int>& e) {
  out << "<expression operator=\"" << ops2str(e.op) << "\" const=\"" << e.term.constant << "\">" << std::endl;
  for (auto const& p : e.term.products) {
    print2xml(out, p);
    out << std::endl;
  }
  out << "</expression>";
}

struct type_visitor : exe::stmt_visitor_t {

  std::string type_string;

  void visit_execution(exe::execution_t& e) override {
    type_string = "-----";
  }

  void visit_assignment(exe::assignment_t& a) override {
    type_string = "assignment";
  }

  void visit_assertion(exe::assertion_t& a) override {
    type_string = "assert";
  }

  void visit_assumption(exe::assumption_t& a) override {
    type_string = "assume";
  }

};

struct xml_output_visitor : exe::stmt_visitor_t {

  std::ostream& out;

  xml_output_visitor(std::ostream& o) : out(o) {

  }

  void visit_execution(exe::execution_t& e) override {
    out << "-----" << std::endl; // TODO make that better
  }

  void visit_assignment(exe::assignment_t& a) override {
    // <lhs variable-id="10"/>
    out << "<lhs variable-id=\"" << a.variable_id << "\"/>" << std::endl;
    out << "<rhs const=\"" << a.rhs.constant << "\">" << std::endl;
    for (auto const& p : a.rhs.products) {
      print2xml(out, p);
      out << std::endl;
    }
    out << "</rhs>" << std::endl;
  }

  void visit_assertion(exe::assertion_t& a) override {
    for (auto const& e : a.exprs) {
      print2xml(out, e);
      out << std::endl;
    }
  }

  void visit_assumption(exe::assumption_t& a) override {
    for (auto const& e : a.exprs) {
      print2xml(out, e);
      out << std::endl;
    }
  }

};

std::ostream& operator<<(std::ostream& out, exe::stmt_t& s) {
  type_visitor v;
  s.accept(v);
  out << "<statement type=\"" << v.type_string << "\" position=\"" << s.position << "\" thread=\"" << s.thread << "\">" << std::endl;

  xml_output_visitor xml_v(out);
  s.accept(xml_v);

  if (s.guard.exprs.size() > 0) {
    out << "<guards size=\"" << s.guard.exprs.size() << "\">" << std::endl;
    for (auto const& e : s.guard.exprs) {
      //out << e << std::endl;
      print2xml(out, e);
      out << std::endl;
    }
    out << "</guards>" << std::endl;
  }

  out << "</statement>";

  return out;
}

std::ostream& operator<<(std::ostream& out, const exe::assertion_t& a) {
  out << "assertion";

  return out;
}

std::ostream& operator<<(std::ostream& out, const exe::assignment_t& a) {
  out << "assignment";

   return out;
}

std::ostream& operator<<(std::ostream& out, const exe::assumption_t& a) {
  out << "assumption";

  return out;
}

std::ostream& operator<<(std::ostream& out, const exe::execution_t& t) {
  out << "<trace nr-of-threads=\"" << t.nr_of_threads << "\">" << std::endl;
  out << "<declarations size=\"" << t.variable_declarations.size() << "\">" << std::endl;
  for (auto const& vd : t.variable_declarations) {
    out << vd << std::endl;
  }
  out << "</declarations>" << std::endl;
  out << "<statements size=\"" << t.statements.size() << "\">" << std::endl;
  for (auto const& s : t.statements) {
    out << *s << std::endl;
  }
  out << "</statements>" << std::endl;
  out << "</trace>";

  return out;
}

char* read_document(const std::string& filename) {

  std::ifstream f(filename.c_str());
  if (f.is_open()) {

    std::string line;
    std::stringstream sstr;
    while (getline(f, line)) {
      sstr << line << std::endl;
    }
    f.close();

    char* data = new char[sstr.str().size() + 1];
    strcpy(data, sstr.str().c_str());

    return data;
  }

  return NULL;
}

exe::variable_declaration_t xml2variable_declaration(rapidxml::xml_node<char>& n_var_decl) {
  exe::variable_declaration_t vd;

  // <variable-declaration id="11" variable="101000000" ssa-index="0" type="int" thread="1"/>
  rapidxml::xml_attribute<char>* id_attr = n_var_decl.first_attribute("id");
  if (!id_attr) { ERROR("No id attribute in variable declaration!"); }
  vd.id = atoi(id_attr->value());

  rapidxml::xml_attribute<char>* variable_attr = n_var_decl.first_attribute("variable");
  if (!variable_attr) { ERROR("No variable attribute in variable declaration!"); }
  vd.variable = atoi(variable_attr->value());

  rapidxml::xml_attribute<char>* ssa_index_attr = n_var_decl.first_attribute("ssa-index");
  if (!ssa_index_attr) { ERROR("No ssa-index attribute in variable declaration!"); }
  vd.ssa_index = atoi(ssa_index_attr->value());

  rapidxml::xml_attribute<char>* type_attr = n_var_decl.first_attribute("type");
  if (!type_attr) { ERROR("No type attribute in variable declaration!"); }

  if (strcmp(type_attr->value(), "int") == 0) {
    vd.type = exe::INT;
  }
  else { ERROR("Unsupported data type in type attribute of variable declaration!"); }

  rapidxml::xml_attribute<char>* thread_attr = n_var_decl.first_attribute("thread");
  if (!thread_attr) { ERROR("No thread attribute in variable declaration!"); }

  if (strcmp(thread_attr->value(), "global") == 0) {
    vd.thread = -1;
  }
  else {
    vd.thread = atoi(thread_attr->value());
  }

  return vd;
}

expr::linear_product_t<int>/*exe::linear_product_t*/ xml2product(rapidxml::xml_node<char>& n_term) {
  expr::linear_product_t<int> p;

  // <term variable-id="12" factor="1"/>

  rapidxml::xml_attribute<char>* var_attr = n_term.first_attribute("variable-id");
  if (!var_attr) { ERROR("Missing variable-id attribute in term!"); }
  p.variable = atoi(var_attr->value());

  rapidxml::xml_attribute<char>* factor_attr = n_term.first_attribute("factor");
  if (!factor_attr) { ERROR("Missing factor attribute in term!"); }
  p.factor = atoi(factor_attr->value());

  return p;
}

expr::expr_t<int> xml2expression(rapidxml::xml_node<char>& n_expr) {
  expr::expr_t<int> e;

  /*
<expression operator="NEQ" const="0">
<term variable-id="7" factor="1"/>
</expression>
  */

  rapidxml::xml_attribute<char>* a_op = n_expr.first_attribute("operator");
  if (!a_op) { ERROR("Missing operator attribute in expression node!"); }
  e.op = str2ops(a_op->value());

  rapidxml::xml_attribute<char>* a_const = n_expr.first_attribute("const");
  if (!a_const) { ERROR("Missing const attribute in expression node!"); }
  e.term.constant = atoi(a_const->value());

  for (rapidxml::xml_node<char>* n_term = n_expr.first_node("term"); n_term; n_term = n_term->next_sibling("term")) {
    e.term.products.push_back(xml2product(*n_term));
  }

  return e;
}

exe::stmt_t* xml2statement(rapidxml::xml_node<char>& n_stmt) {

  exe::stmt_t* s;// = new exe::statement_t;

  rapidxml::xml_attribute<char>* type_attr = n_stmt.first_attribute("type");
  if (!type_attr) { ERROR("No type attribute in statement!"); }

  if (strcmp(type_attr->value(), "assignment") == 0) {
    exe::assignment_t* a = new exe::assignment_t;
    //s->type = exe::ASSIGNMENT;

    rapidxml::xml_node<char>* n_lhs = n_stmt.first_node("lhs");
    if (!n_lhs) { ERROR("No lhs in assignment!"); }

    rapidxml::xml_attribute<char>* n_var_id_attr = n_lhs->first_attribute("variable-id");
    if (!n_var_id_attr) { ERROR("No variable-id attribute in lhs of assignment!"); }
    a->variable_id = atoi(n_var_id_attr->value());

    rapidxml::xml_node<char>* n_rhs = n_stmt.first_node("rhs");
    if (!n_rhs) { ERROR("No rhs in assignment!"); }

    // a) extract const value
    rapidxml::xml_attribute<char>* n_const_attr = n_rhs->first_attribute("const");
    if (!n_const_attr) { ERROR("No const attribute in rhs of assignment!"); }
    a->rhs.constant = atoi(n_const_attr->value());

    // b) extract terms
    for (rapidxml::xml_node<char>* n_term = n_rhs->first_node("term"); n_term; n_term = n_term->next_sibling("term")) {
      a->rhs.products.push_back(xml2product(*n_term));
    }

    s = a;
  }
  else if (strcmp(type_attr->value(), "assert") == 0) {
    exe::assertion_t* a  = new exe::assertion_t;
    //s->type = exe::ASSERTION;

    // extract expressions
    for (rapidxml::xml_node<char>* n_expr = n_stmt.first_node("expression"); n_expr; n_expr = n_expr->next_sibling("expression")) {
      a->exprs.push_back(xml2expression(*n_expr));
    }

    s = a;
  }
  else if (strcmp(type_attr->value(), "assume") == 0) {
    exe::assumption_t* a = new exe::assumption_t;
    //s->type = exe::ASSUMPTION;

    // extract expressions
    for (rapidxml::xml_node<char>* n_expr = n_stmt.first_node("expression"); n_expr; n_expr = n_expr->next_sibling("expression")) {
      a->exprs.push_back(xml2expression(*n_expr));
    }

    s = a;
  }
  else {
    ERROR("Unknown value for type attribute in statement!");
  }

  rapidxml::xml_attribute<char>* position_attr = n_stmt.first_attribute("position");
  if (!position_attr) { ERROR("No position attribute in statement!"); }
  s->position = atoi(position_attr->value());

  rapidxml::xml_attribute<char>* thread_attr = n_stmt.first_attribute("thread");
  if (!thread_attr) { ERROR("No thread attribute in statement!"); }
  s->thread = atoi(thread_attr->value());


  rapidxml::xml_node<char>* n_guards = n_stmt.first_node("guards");
  if (n_guards) {
    for (rapidxml::xml_node<char>* n_expr = n_guards->first_node("expression"); n_expr; n_expr = n_expr->next_sibling("expression")) {
      s->guard.exprs.push_back(xml2expression(*n_expr));
    }

    rapidxml::xml_attribute<char>* a_guards_size = n_guards->first_attribute("size");
    if (!a_guards_size) { ERROR("Missing size in guards node!"); }
    int tmp_guards_size = atoi(a_guards_size->value());
    if (tmp_guards_size != (int)s->guard.exprs.size()) { ERROR("Size of guards does not match size attribute!"); }
  }

  return s;
}

exe::execution_t xml2execution(rapidxml::xml_node<char>& n_trace) {
  exe::execution_t t;

  // extract number of threads
  rapidxml::xml_attribute<char>* n_nr_of_threads_attrib = n_trace.first_attribute("nr-of-threads");
  if (!n_nr_of_threads_attrib) { ERROR("Missing number-of-threads attribute in trace node!"); }
  t.nr_of_threads = atoi(n_nr_of_threads_attrib->value());

  // extract variable declarations
  rapidxml::xml_node<char>* n_var_decls = n_trace.first_node("declarations");
  if (!n_var_decls) { ERROR("No variable declaration node!"); }

  for (
    rapidxml::xml_node<char>* n_var_decl = n_var_decls->first_node("variable-declaration");
    n_var_decl;
    n_var_decl = n_var_decl->next_sibling("variable-declaration")
  ) {
    t.variable_declarations.push_back(xml2variable_declaration(*n_var_decl));
  }

  rapidxml::xml_attribute<char>* a_nr_of_vds = n_var_decls->first_attribute("size");
  if (!a_nr_of_vds) { ERROR("Missing number of variable declarations!"); }
  int tmp_nr_of_vds = atoi(a_nr_of_vds->value());
  if (tmp_nr_of_vds != (int)t.variable_declarations.size()) { ERROR("Number of variable declarations does not match!"); }


  // extract statements
  rapidxml::xml_node<char>* n_stmts = n_trace.first_node("statements");
  if (!n_stmts) { ERROR("No statements node!"); }

  for (
    rapidxml::xml_node<char>* n_stmt = n_stmts->first_node("statement");
    n_stmt;
    n_stmt = n_stmt->next_sibling("statement")
  ) {
    t.statements.push_back(xml2statement(*n_stmt));
  }

  rapidxml::xml_attribute<char>* a_nr_of_stmts = n_stmts->first_attribute("size");
  if (!a_nr_of_stmts) { ERROR("Missing number of statements!"); }
  int tmp_nr_of_stmts = atoi(a_nr_of_stmts->value());
  if (tmp_nr_of_stmts != (int)t.statements.size()) { ERROR("Number of statements does not match!"); }


  return t;
}

exe::execution_t read_execution(const char* xml_file) {
  char* document_string = read_document(xml_file);
  if (!document_string) {
    std::stringstream sstr;
    sstr << "Error reading file \"" << xml_file << "\"!";
    ERROR(sstr.str().c_str());
  }

  rapidxml::xml_document<char> doc;
  doc.parse<0>(document_string);

  exe::execution_t t = xml2execution(*doc.first_node());

  delete[] document_string;

  return t;
}
