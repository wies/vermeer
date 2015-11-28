#ifndef XML_H_INCLUDED
#define XML_H_INCLUDED

#include <string>
#include <ostream>

#include "rapidxml-1.13/rapidxml.hpp"

#include "trace.h"

ops str2ops(const char* str);
std::string ops2str(ops o);
std::string stmttype2str(statement_type_t t);

std::ostream& operator<<(std::ostream& out, const variable_declaration_t& vd);
std::ostream& operator<<(std::ostream& out, const product_t& p);
std::ostream& operator<<(std::ostream& out, const expression_t& e);
std::ostream& operator<<(std::ostream& out, const statement_t& s);
std::ostream& operator<<(std::ostream& out, const trace_t& t);

char* read_document(const std::string& filename);

variable_declaration_t extract_variable_declaration(rapidxml::xml_node<char>& n_var_decl);
product_t extract_product(rapidxml::xml_node<char>& n_term);
expression_t extract_expression(rapidxml::xml_node<char>& n_expr);
statement_t extract_statement(rapidxml::xml_node<char>& n_stmt);
trace_t extract_trace(rapidxml::xml_node<char>& n_trace);

trace_t read_trace(const char* xml_file);

#endif // XML_H_INCLUDED
