#include <cstdlib>
#include <iostream>

#include <map>
#include <vector>

#include "error.h"
#include "trace.h"
#include "xml.h"

#if 0
struct thread_id_t {

  const int unique_id;

  inline
  bool operator==(const thread_id_t& other) const {
    return unique_id == other.unique_id;
  }

  inline
  bool operator!=(const thread_id_t& other) const {
    return !(*this == other);
  }

  inline
  bool operator<(const thread_id_t& other) const {
    return unique_id < other.unique_id;
  }

};
#endif

struct thread_local_position_t {
  //thread_id_t thread;
  int thread;
  int position;

  friend std::ostream& operator<<(std::ostream& out, const thread_local_position_t p) {
    out << "(T" << p.thread << ",P" << p.position << ")";
    return out;
  }
};

std::vector<thread_local_position_t> extract_thread_local_positions(const execution_t& e) {
  std::vector<thread_local_position_t> v;


  std::map<int, int> thread_local_counters;

  // TODO do we assume that statements are ordered according to their position attribute?
  for (auto const& s : e.statements) {
    int pos = thread_local_counters[s.thread];
    v.push_back({ s.thread, pos });
    thread_local_counters[s.thread] = pos + 1;
  }

  return v;
}

int main(int argc, char* argv[]) {
  execution_t e = read_execution("example.xml");

  std::cout << e << std::endl;

  auto pos = extract_thread_local_positions(e);

  for (auto const& p : pos) {
    std::cout << p << std::endl;
  }

  return EXIT_SUCCESS;
}

