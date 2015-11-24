#include <cstdlib>
#include <cstring>
#include <string>
#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>

#include "rapidxml-1.13/rapidxml.hpp"

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

struct multiplication_t {
  int variable_id;
  int factor;
};

struct term_t {
  std::vector<multiplication_t> mults;
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
};

struct trace_t {
  std::vector<variable_declaration_t> variable_declarations;
  std::vector<statement_t> statements;
};

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

  if (id_attr) {
    vd.id = atoi(id_attr->value());
  }
  else {
    // TODO error handling
  }

  rapidxml::xml_attribute<char>* variable_attr = n_var_decl.first_attribute("variable");

  if (variable_attr) {
    vd.variable = atoi(variable_attr->value());
  }
  else {
    // TODO error handling
  }

  rapidxml::xml_attribute<char>* ssa_index_attr = n_var_decl.first_attribute("ssa-index");

  if (ssa_index_attr) {
    vd.ssa_index = atoi(ssa_index_attr->value());
  }
  else {
    // TODO error handling
  }

  rapidxml::xml_attribute<char>* type_attr = n_var_decl.first_attribute("type");

  if (type_attr) {
    if (strcmp(type_attr->value(), "int") == 0) {
      vd.type = INT;
    }
    else {
      // TODO error handling
    }
  }
  else {
    // TODO error handling
  }

  rapidxml::xml_attribute<char>* thread_attr = n_var_decl.first_attribute("thread");

  if (thread_attr) {
    if (strcmp(thread_attr->value(), "global") == 0) {
      vd.thread = -1;
    }
    else {
      vd.thread = atoi(thread_attr->value());
    }
  }
  else {
    // TODO error handling
  }

  return vd;
}

statement_t extract_statement(rapidxml::xml_node<char>& n_stmt) {
  statement_t s;

  return s;
}

trace_t extract_trace(rapidxml::xml_node<char>& n_trace) {
  trace_t t;

  rapidxml::xml_node<char>* n_variable_declarations = n_trace.first_node("declarations");

  if (n_variable_declarations) {
    for (
      rapidxml::xml_node<char>* n_var_declaration = n_variable_declarations->first_node("variable-declaration");
      n_var_declaration;
      n_var_declaration = n_var_declaration->next_sibling("variable-declaration")
    ) {
      t.variable_declarations.push_back(extract_variable_declaration(*n_var_declaration));
    }
  }
  else {
    // TODO error handling
  }

  rapidxml::xml_node<char>* n_statements = n_trace.first_node("statements");

  if (n_statements) {
    for (
      rapidxml::xml_node<char>* n_statement = n_statements->first_node("statement");
      n_statement;
      n_statement = n_statement->next_sibling("statement")
    ) {
      t.statements.push_back(extract_statement(*n_statement));
    }
  }
  else {
    // TODO error handling
  }

  return t;
}

int main(int argc, char* argv[]) {

  char* document_string = read_document("example.xml");

  if (!document_string) {
    std::cerr << "Error reading file \"example.xml\"" << std::endl;
    return EXIT_FAILURE;
  }

  std::cout << document_string << std::endl;

  rapidxml::xml_document<char> doc;
  doc.parse<0>(document_string);

  trace_t t = extract_trace(*doc.first_node());

  std::cout << "t.statements.size() = " << t.statements.size() << std::endl;
  std::cout << "t.variable_declarations.size() = " << t.variable_declarations.size() << std::endl;

  for (auto const& vd : t.variable_declarations) {
    std::cout << vd << std::endl;
  }

  delete[] document_string;

  return EXIT_SUCCESS;
}

