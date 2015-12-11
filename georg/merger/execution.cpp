#include "execution.h"

namespace exe {

assignment_t::~assignment_t() {}

void assignment_t::accept(stmt_visitor_t& v) {
  v.visit_assignment(*this);
}

assertion_t::~assertion_t() {}

void assertion_t::accept(stmt_visitor_t& v) {
  v.visit_assertion(*this);
}

assumption_t::~assumption_t() {}

void assumption_t::accept(stmt_visitor_t& v) {
  v.visit_assumption(*this);
}

execution_t::~execution_t() {
  for (auto& s : statements) {
    delete s;
  }
}

void execution_t::accept(stmt_visitor_t& v) {
  v.visit_execution(*this);
}

}
