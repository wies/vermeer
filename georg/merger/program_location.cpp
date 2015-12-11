#include "program_location.h"

#include <ostream>

thread_local_position_t& thread_local_position_t::operator=(const thread_local_position_t& p) {
  thread = p.thread;
  position = p.position;
  return *this;
}

bool thread_local_position_t::operator==(const thread_local_position_t& p) const {
  return (thread == p.thread && position == p.position);
}

bool thread_local_position_t::operator!=(const thread_local_position_t& p) const {
  return !(*this == p);
}

std::ostream& operator<<(std::ostream& out, const thread_local_position_t p) {
  out << "(T" << p.thread << ",P" << p.position << ")";
  return out;
}
