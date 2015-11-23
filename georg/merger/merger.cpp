#include <cstdlib>
#include <cstring>
#include <string>
#include <iostream>
#include <fstream>
#include <sstream>

#include "rapidxml-1.13/rapidxml.hpp"

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

int main(int argc, char* argv[]) {

  char* document_string = read_document("example.xml");

  if (!document_string) {
    std::cerr << "Error reading file \"example.xml\"" << std::endl;
    return EXIT_FAILURE;
  }

  std::cout << document_string << std::endl;

  rapidxml::xml_document<char> doc;
  doc.parse<0>(document_string);

  std::cout << doc.first_node()->name() << std::endl;

  rapidxml::xml_node<char>* n = doc.first_node()->first_node("declarations");

  if (n) {
    std::cout << n->name() << std::endl;
  }

  delete[] document_string;

  return EXIT_SUCCESS;
}

