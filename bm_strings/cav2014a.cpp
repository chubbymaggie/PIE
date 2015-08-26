#include "bm_strings.h"

int main() {
  int i;
  string r;
  INITIALIZE("%d \t %s\n", i, r.c_str());

  i = 0;
  set(r, "a");

  while(unknown()) {
    PRINT_VARS();
    set(r, cat(cat("(", r), ")"));
    ++i;
  }
  PRINT_VARS();

  assert(len(r) == 2*i + 1);
  if(i > 0)
    assert(has(r, "(a)"));
  return 0;
}
