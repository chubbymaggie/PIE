#include "bm_oopsla.h"

int main() {
  int n, i, k, j = 0;
  INITIALIZE(4, i, j, k, n);

  n = unknown();
  assume(n > 0);
  assume(k > n);

  while(j < n) {
    PRINT_VARS();
    j++;
    k--;
  }
  PRINT_VARS();

  assert(k >= 0);
  return 0;
}
