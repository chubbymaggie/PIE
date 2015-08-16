#include "../bm_strings.h"

int main() {
  int i, j, x;
  string s0, r;
  INITIALIZE("%d \t %d \t  %d \t %s \t %s\n", i, x, j, s0.c_str(), r.c_str());

  s0 = unknown_s();
  i = unknown();
  j = unknown();

  assume(s0.length() > 0);
  assume(i >= 0);
  assume(j >= i);
  assume(i < s0.length());
  assume(j < s0.length());

  x = i;
  r = "";

  while(x <= j) {
    PRINT_VARS();
    r += s0.at(x);
    ++x;
  }
  PRINT_VARS();

  assert(r == s0.substr(i, j - i + 1));
  return 0;
}
