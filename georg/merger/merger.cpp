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

struct variable_declarations_t {
  std::vector<variable_declaration_t> decls;
};

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
    rapidxml::xml_node<char>* n_var_declaration = n_variable_declarations->first_node("variable-declaration");

    while (n_var_declaration) {
      t.variable_declarations.push_back(extract_variable_declaration(*n_var_declaration));
      n_var_declaration = n_var_declaration->next_sibling("variable-declaration");
    }
  }
  else {
    // TODO error handling
  }

  rapidxml::xml_node<char>* n_statements = n_trace.first_node("statements");

  if (n_statements) {
    rapidxml::xml_node<char>* n_statement = n_statements->first_node("statement");

    while (n_statement) {
      t.statements.push_back(extract_statement(*n_statement));
      n_statement = n_statement->next_sibling("statement");
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

  delete[] document_string;

  return EXIT_SUCCESS;
}

