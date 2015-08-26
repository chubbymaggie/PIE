#include "bm_strings.h"

int main() {
  int i;
  string r;
  INITIALIZE("%d \t %s\n", i, r.c_str());

  r = unknown_s2();

  i = len(r);

  while(ind(r, "aa") >= 0) {
    PRINT_VARS();
    set(r, rep(r, "aa", ")"));
    set(r, cat(r, "a"));
  }
  PRINT_VARS();

  assert(len(r) == i);
  assert(!has(r, "aa"));
  return 0;
}
