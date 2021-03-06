#ifndef PROGRAM_LOCATION_H_INCLUDED
#define PROGRAM_LOCATION_H_INCLUDED

#include <ostream>

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

  thread_local_position_t& operator=(const thread_local_position_t& p);

  bool operator==(const thread_local_position_t& p) const;
  bool operator!=(const thread_local_position_t& p) const;

  friend std::ostream& operator<<(std::ostream& out, const thread_local_position_t p);
};

#endif // PROGRAM_LOCATION_H_INCLUDED
