#include "../bm_strings.h"

int main() {
  int i;
  string r;
  INITIALIZE("%d \t %s\n", i, r.c_str());

  i = 0;
  r = "a";

  while(unknown()) {
    PRINT_VARS();
    r = "(" + r + ")";
    ++i;
  }
  PRINT_VARS();

  assert(r.length() == 2*i + 1);
  if(i > 0)
    assert(contains(r, "a"));
  return 0;
}
