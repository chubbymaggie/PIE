#include "bm_strings.h"

int main() {
  int i;
  string s0, s1, r;
  INITIALIZE("%d \t %s \t %s \t %s\n", i, s0.c_str(), s1.c_str(), r.c_str());

  s0 = unknown_s();
  s1 = unknown_s();

  i = 0;
  r = s0;

  while(i < s1.length()) {
    PRINT_VARS();
    r += s1.at(i);
    ++i;
  }
  PRINT_VARS();

  assert(r == s0 + s1);
  return 0;
}
