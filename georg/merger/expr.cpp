#include "expr.h"

#include "error.h"

#include <cstring>
#include <string>

namespace expr {

ops str2ops(const char* str) {
  ops o;

  if (strcmp(str, "EQ") == 0) {
    o = EQ;
  }
  else if (strcmp(str, "NEQ") == 0) {
    o = NEQ;
  }
  else if (strcmp(str, "LT") == 0) {
    o = LT;
  }
  else if (strcmp(str, "LEQ") == 0) {
    o = LEQ;
  }
  else if (strcmp(str, "GT") == 0) {
    o = GT;
  }
  else if (strcmp(str, "GEQ") == 0) {
    o = GEQ;
  }
  else {
    ERROR("Unrecognized expression operator!");
  }

  return o;
}

std::string ops2str(ops o) {
  std::string s;

  switch (o) {
    case EQ:
      s = "EQ";
      break;
    case NEQ:
      s = "NEQ";
      break;
    case LT:
      s = "LT";
      break;
    case LEQ:
      s = "LEQ";
      break;
    case GT:
      s = "GT";
      break;
    case GEQ:
      s = "GEQ";
      break;
    default:
      ERROR("Unrecognized operator!");
  }

  return s;
}

std::string ops2strC(ops o) {
  std::string s;

  switch (o) {
    case EQ:
      s = "==";
      break;
    case NEQ:
      s = "!=";
      break;
    case LT:
      s = "<";
      break;
    case LEQ:
      s = "<=";
      break;
    case GT:
      s = ">";
      break;
    case GEQ:
      s = ">=";
      break;
    default:
      ERROR("Unrecognized operator!");
  }

  return s;
}

}
