#ifndef ERROR_H_INCLUDED
#define ERROR_H_INCLUDED

void merge_error(const char* file, int line, const char* text) {
  std::cerr << std::endl << "*** ERROR at line " << line << " in file \"" << file << "\": " << text << std::endl;
  exit(EXIT_FAILURE);
}

#define ERROR(text) merge_error(__FILE__, __LINE__, text)

#endif // ERROR_H_INCLUDED
