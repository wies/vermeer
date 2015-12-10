#ifndef EXECUTION2ALPHABET_H_INCLUDED
#define EXECUTION2ALPHABET_H_INCLUDED

#include "execution.h"
#include "alphabet.h"

#include <map>
#include <ostream>
#include <vector>

struct projected_execution_t {

  std::map<int, std::vector<alphabet::stmt_t*>> projections;
  const int unique_id; // the id has to be unique across all other executions
  // TODO make it a static member and increment when creating an object?
  // TODO the way we do it now makes a correct copy constructor and assignment operator impossible

  projected_execution_t(exe::execution_t& e, int unique_id_);
  ~projected_execution_t();

  friend std::ostream& operator<<(std::ostream& out, const projected_execution_t& p);

};

struct projected_executions_t {

  projected_executions_t(const projected_execution_t& pexe);

  /*
    We assume that every symbol in the alphabet appears at most once in a word,
    that there is a total order over the symbols in the alphabet, and that in
    each word the symbols respect this order.
  */
  void merge(
    const projected_execution_t& pexe,
    std::function<bool (const graph_t<alphabet::stmt_t*>::edge_t&, const alphabet::stmt_t&)> is_mergable,
    std::function<void (const graph_t<alphabet::stmt_t*>::edge_t&, const alphabet::stmt_t&)> do_merge
  );

  friend std::ostream& operator<<(std::ostream& out, const projected_executions_t ps);

private:
  std::map<int, graph_t<alphabet::stmt_t*>> projections;
  std::map<int, std::vector< graph_t<alphabet::stmt_t*>::edge_t >> edges;

};

struct local_execution_extractor_t : public exe::stmt_visitor_t {

  local_execution_extractor_t(projected_execution_t& p);

  int get_ssa_index(int thread, int variable);
  void set_ssa_index(int thread, int variable, int index);

  enum term_purity {

    CONSTANT_ONLY,
    LOCAL_ONLY,
    SHARED_ONLY,
    MIXED

  };

  term_purity determine_purity(expr::term_t<int> t);

  void visit_execution(exe::execution_t& e) override;
  void visit_assignment(exe::assignment_t& a) override;
  void visit_assertion(exe::assertion_t& a) override;
  void visit_assumption(exe::assumption_t& a) override;

private:
  std::map<int, std::vector<alphabet::stmt_t*>>& local_executions;
  int execution_id;
  std::vector<exe::variable_declaration_t> variable_declarations;
  std::map<int, std::map<int, int>> thread_local_ssa_indices;
  expr::variable_substitution_t<int, alphabet::ssa_variable_t> vsubst;

};

#endif // EXECUTION2ALPHABET_H_INCLUDED
