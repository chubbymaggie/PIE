#include "bm_oopsla.h"

int main() {
  int n, j, k, l = 0;
  INITIALIZE(4, j, k, l, n);

  assume(n > 0);
  j = k = n;

  while(j > l) {
    PRINT_VARS();
    j--;
    k--;
  }
  PRINT_VARS();

  assert(k >= l);
  return 0;
}