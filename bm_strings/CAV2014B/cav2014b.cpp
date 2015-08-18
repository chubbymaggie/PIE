#include "../bm_strings.h"

int main() {
  int i;
  string r;
  INITIALIZE("%d \t %s\n", i, r.c_str());

  r = unknown_s2();

  i = r.length();

  while(indexOf(r, "aa") >= 0) {
    PRINT_VARS();
    r = replace(r, "aa", ")");
    r += "a";
  }
  PRINT_VARS();

  assert(r.length() == i);
  assert(!contains(r, "aa"));
  return 0;
}
