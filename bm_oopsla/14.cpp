#include "bm_oopsla.h"

int main() {
  int c1 = 4, c2 = 2;
  int n, v, i = 0, k = 0;
  INITIALIZE("(%d, %d, %d, %d, %d, %d)", c1, c2, i, k, n, v);

  assume(n > 0);

  while(i < n) {
    PRINT_VARS();
    i++;
    // if(unknown2() % 2 == 0) v = 0;
    if(unknown2()) v = 0;
    else           v = 1;

    if(v == 0)  k += c1;
    else        k += c2;
  }
  PRINT_VARS();

  assert(k > n);
  return 0;
}
