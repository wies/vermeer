#include "execution2alphabet.h"

// TODO make parameter e const! How to change accept?
projected_execution_t::projected_execution_t(exe::execution_t& e) {
  local_execution_extractor_t lee(*this);
  e.accept(lee);
}

projected_execution_t::~projected_execution_t() {
  for (auto& p : projections) {
    for (auto& s : p.second) {
      delete s;
    }
  }
}
