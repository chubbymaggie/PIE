#include "bm_strings.h"

int main() {
  int i;
  string r;
  INITIALIZE("%d \t %s\n", i, r.c_str());

  i = 0;
  set(r, "a");

  while(unknown()) {
    PRINT_VARS();
    set(r, rep(r, "a", "aa"));
    ++i;
  }
  PRINT_VARS();

  assert(len(r) > i);
  return 0;
}
