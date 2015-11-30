#ifndef ALPHABET_H_INCLUDED
#define ALPHABET_H_INCLUDED

namespace alphabet {

struct ssa_variable_t {
  int unique_id;
  int variable_id;
  /* type, currently: INT */
  int thread_id;
  int ssa_index;
};

enum stmt_type_t {
  PI_ASSIGNMENT, /*PHI_ASSIGNMENT,*/ LOCAL_ASSIGNMENT
};

struct pi_assignment_t {
  ssa_variable_t variable;
};

struct local_assignment_t {
  ssa_variable_t variable;
  /* ... */
};

}

#endif // ALPHABET_H_INCLUDED
