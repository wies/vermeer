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
#include "xml.h"

int main(int argc, char* argv[]) {

  char* document_string = read_document("example.xml");
  if (!document_string) { ERROR("Error reading file \"example.xml\"!"); }

  rapidxml::xml_document<char> doc;
  doc.parse<0>(document_string);

  trace_t t = extract_trace(*doc.first_node());

  std::cout << t << std::endl;

  delete[] document_string;

  return EXIT_SUCCESS;
}

