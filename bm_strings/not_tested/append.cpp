#include "bm_strings.h"

int main() {
  int i;
  string s0, s1, r;
  INITIALIZE("%d \t %s \t %s \t %s\n", i, s0.c_str(), s1.c_str(), r.c_str());

  s0 = unknown_s();
  s1 = unknown_s();

  i = 0;
  set(r, s0);

  while(i < len(s1)) {
    PRINT_VARS();
    set(r, cat(r, get(s1, i)));
    ++i;
  }
  PRINT_VARS();

  assert(eql(r, cat(s0, s1)));
  return 0;
}
