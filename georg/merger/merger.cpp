#include <cstdlib>
#include <cstring>
#include <string>
#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>

#include "rapidxml-1.13/rapidxml.hpp"

void merge_error(const char* file, int line, const char* text) {
  std::cerr << std::endl << "*** ERROR at line " << line << " in file \"" << file << "\": " << text << std::endl;
  exit(EXIT_FAILURE);
}

#define ERROR(text) merge_error(__FILE__, __LINE__, text)

enum variable_types_t {
  INT
};

struct variable_declaration_t {
  int id;
  int variable;
  int ssa_index;
  variable_types_t type;
  int thread;
};

std::ostream& operator<<(std::ostream& out, const variable_declaration_t& vd) {
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
      << "ssa_index=\"" << vd.ssa_index << "\" "
      << "type=\"int\" "
      << "thread=\"" << thread_str << "\"/>";

  return out;
}

struct product_t {
  int variable_id;
  int factor;
};

struct term_t {
  std::vector<product_t> mults;
  int constant;
};

enum ops {
  EQ, NEQ, LT, LEQ, GT, GEQ
};

struct expression_t {
  ops op;
  term_t term;
};

struct guard_t {
  std::vector<expression_t> exprs;
};

enum statement_type_t {
  ASSIGNMENT, ASSERTION, ASSUMPTION
};

struct statement_t {
  statement_type_t type;
  int variable_id;
  term_t rhs;
  guard_t guard;
  int position;
  int thread;
};

std::ostream& operator<<(std::ostream& out, const statement_t& s) {

  std::string type_str;
  switch (s.type) {
    case ASSIGNMENT:
      type_str = "assignment";
      break;
    case ASSERTION:
      type_str = "assertion";
      break;
    case ASSUMPTION:
      type_str = "assumption";
      break;
  }

  out << "<statement type=\"" << type_str << "\" position=\"" << s.position << "\" thread=\"" << s.thread << "\">" << std::endl;
  out << "</statement>";

  return out;
}

struct trace_t {
  std::vector<variable_declaration_t> variable_declarations;
  std::vector<statement_t> statements;
  int nr_of_threads;
};

std::ostream& operator<<(std::ostream& out, const trace_t& t) {
  out << "<trace nr-of-threads=\"" << t.nr_of_threads << "\">" << std::endl;
  out << "<declarations size=\"" << t.variable_declarations.size() << "\">" << std::endl;
  for (auto const& vd : t.variable_declarations) {
    out << vd << std::endl;
  }
  out << "</declarations>" << std::endl;
  out << "<statements size=\"" << t.statements.size() << "\">" << std::endl;
  for (auto const& s : t.statements) {
    out << s << std::endl;
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

variable_declaration_t extract_variable_declaration(rapidxml::xml_node<char>& n_var_decl) {
  variable_declaration_t vd;

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
    vd.type = INT;
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

product_t extract_product(rapidxml::xml_node<char>& n_term) {
  product_t p;

  // <term variable-id="12" factor="1"/>

  rapidxml::xml_attribute<char>* var_attr = n_term.first_attribute("variable-id");
  if (!var_attr) { ERROR("Missing variable-id attribute in term!"); }
  p.variable_id = atoi(var_attr->value());

  rapidxml::xml_attribute<char>* factor_attr = n_term.first_attribute("factor");
  if (!factor_attr) { ERROR("Missing factor attribute in term!"); }
  p.factor = atoi(factor_attr->value());

  return p;
}

statement_t extract_statement(rapidxml::xml_node<char>& n_stmt) {

  statement_t s;

  rapidxml::xml_attribute<char>* type_attr = n_stmt.first_attribute("type");
  if (!type_attr) { ERROR("No type attribute in statement!"); }

  if (strcmp(type_attr->value(), "assignment") == 0) {
    s.type = ASSIGNMENT;

    rapidxml::xml_node<char>* n_lhs = n_stmt.first_node("lhs");
    if (!n_lhs) { ERROR("No lhs in assignment!"); }

    rapidxml::xml_attribute<char>* n_var_id_attr = n_lhs->first_attribute("variable-id");
    if (!n_var_id_attr) { ERROR("No variable-id attribute in lhs of assignment!"); }
    s.variable_id = atoi(n_var_id_attr->value());

    rapidxml::xml_node<char>* n_rhs = n_stmt.first_node("rhs");
    if (!n_rhs) { ERROR("No rhs in assignment!"); }

    // a) extract const value
    rapidxml::xml_attribute<char>* n_const_attr = n_rhs->first_attribute("const");
    if (!n_const_attr) { ERROR("No const attribute in rhs of assignment!"); }
    s.rhs.constant = atoi(n_const_attr->value());

    // b) extract terms
    for (rapidxml::xml_node<char>* n_term = n_rhs->first_node("term"); n_term; n_term = n_term->next_sibling("term")) {
      s.rhs.mults.push_back(extract_product(*n_term));
    }
  }
  else if (strcmp(type_attr->value(), "assert") == 0) {
    s.type = ASSERTION;

    // TODO handle assertion specific things

  }
  else if (strcmp(type_attr->value(), "assume") == 0) {
    s.type = ASSUMPTION;

    // TODO handle assumption specific things

  }
  else {
    ERROR("Unknown value for type attribute in statement!");
  }

  rapidxml::xml_attribute<char>* position_attr = n_stmt.first_attribute("position");
  if (!position_attr) { ERROR("No position attribute in statement!"); }
  s.position = atoi(position_attr->value());

  rapidxml::xml_attribute<char>* thread_attr = n_stmt.first_attribute("thread");
  if (!thread_attr) { ERROR("No thread attribute in statement!"); }
  s.thread = atoi(thread_attr->value());

  // TODO extract guards

  return s;
}

trace_t extract_trace(rapidxml::xml_node<char>& n_trace) {
  trace_t t;

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
    t.variable_declarations.push_back(extract_variable_declaration(*n_var_decl));
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
    t.statements.push_back(extract_statement(*n_stmt));
  }

  rapidxml::xml_attribute<char>* a_nr_of_stmts = n_stmts->first_attribute("size");
  if (!a_nr_of_stmts) { ERROR("Missing number of statements!"); }
  int tmp_nr_of_stmts = atoi(a_nr_of_stmts->value());
  if (tmp_nr_of_stmts != (int)t.statements.size()) { ERROR("Number of statements does not match!"); }


  return t;
}

int main(int argc, char* argv[]) {

  char* document_string = read_document("example.xml");
  if (!document_string) { ERROR("Error reading file \"example.xml\"!"); }

  std::cout << document_string << std::endl;

  rapidxml::xml_document<char> doc;
  doc.parse<0>(document_string);

  trace_t t = extract_trace(*doc.first_node());

  std::cout << t << std::endl;

  delete[] document_string;

  return EXIT_SUCCESS;
}

