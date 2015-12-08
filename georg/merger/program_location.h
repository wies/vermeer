#ifndef PROGRAM_LOCATION_H_INCLUDED
#define PROGRAM_LOCATION_H_INCLUDED

struct thread_local_position_t {
  //thread_id_t thread;
  int thread;
  int position;

  friend std::ostream& operator<<(std::ostream& out, const thread_local_position_t p) {
    out << "(T" << p.thread << ",P" << p.position << ")";
    return out;
  }
};

#endif // PROGRAM_LOCATION_H_INCLUDED
