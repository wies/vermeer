#include "graph.h"

#include <cstdlib>
#include <iostream>

int main(int argc, char* argv[]) {

  graph_t<int> g;

  g.create_node();
  g.create_node();
  g.add_edge(0, 5, 1);
  g.add_edge(0, 10, 1);

  std::cout << g << std::endl;

  return EXIT_SUCCESS;
}
