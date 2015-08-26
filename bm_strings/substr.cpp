#include "bm_strings.h"

int main() {
  int i, j, x;
  string s0, r;
  INITIALIZE("%d \t %d \t  %d \t %s \t %s\n", i, x, j, s0.c_str(), r.c_str());

  s0 = unknown_s();

  assume(len(s0) > 0);

  i = unknown(0, len(s0)-1);
  j = unknown(i, len(s0)-1);

  x = i;
  set(r, "");

  while(x <= j) {
    PRINT_VARS();
    set(r, cat(r, get(s0, x)));
    ++x;
  }
  PRINT_VARS();

  assert(eql(r, sub(s0, i, j - i + 1)));
  return 0;
}
