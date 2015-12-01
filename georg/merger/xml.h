#ifndef XML_H_INCLUDED
#define XML_H_INCLUDED

#include <string>
#include <ostream>

#include "rapidxml-1.13/rapidxml.hpp"

#include "trace.h"

std::ostream& operator<<(std::ostream& out, const exe::variable_declaration_t& vd);
std::ostream& operator<<(std::ostream& out, const exe::linear_product_t& p);
std::ostream& operator<<(std::ostream& out, const exe::expression_t& e);
std::ostream& operator<<(std::ostream& out, const exe::statement_t& s);
std::ostream& operator<<(std::ostream& out, const exe::execution_t& t);

exe::execution_t read_execution(const char* xml_file);

#endif // XML_H_INCLUDED
