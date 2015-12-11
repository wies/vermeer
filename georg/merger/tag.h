#ifndef TAG_H_INCLUDED
#define TAG_H_INCLUDED

#include <ostream>

template <class Tagged>
struct execution_tag_t {

  execution_tag_t(Tagged t_, int execution_id_) : t(t_), eid(execution_id_) {}
  execution_tag_t(const execution_tag_t& other) : t(other.t), eid(other.eid) {}

  const Tagged& element() const {
    return t;
  }

  int execution_id() const {
    return eid;
  }

  inline
  bool operator==(const execution_tag_t& other) const {
    return (eid == other.eid && t == other.t);
  }

  inline
  bool operator!=(const execution_tag_t& other) const {
    return !(*this == other);
  }

  friend std::ostream& operator<<(std::ostream& out, const execution_tag_t& t) {
    out << t.t << "@" << t.eid;
    return out;
  }

private:
  Tagged t;
  int eid;

};

#endif // TAG_H_INCLUDED
