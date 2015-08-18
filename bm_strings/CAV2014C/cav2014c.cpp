#include "../bm_strings.h"

int main() {
  int i;
  string r;
  INITIALIZE("%d \t %s\n", i, r.c_str());

  i = 0;
  r = "a";

  while(unknown()) {
    PRINT_VARS();
    r = replace(r, "a", "aa");
    ++i;
  }
  PRINT_VARS();

  assert(r.length() > i);
  return 0;
}
