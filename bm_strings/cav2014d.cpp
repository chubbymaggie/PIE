#include "bm_strings.h"

int main() {
  int i;
  string r;
  INITIALIZE("%d \t %s\n", i, r.c_str());

  set(r, "a");
  i = len(r);

  while(unknown()) {
    PRINT_VARS();
    set(r, cat(r, "x"));
  }
  PRINT_VARS();

  assert(eql(sub(r, 0, i), "a"));
  return 0;
}
