#include "bm_oopsla.h"

int main() {
  int n, i, k, j = 0;
  INITIALIZE("(%d, %d, %d, %d)\n", i, j, k, n);

  assume(n, n > 0);
  assume(k, k > n);

  while(j < n) {
    PRINT_VARS();
    j++;
    k--;
  }
  PRINT_VARS();

  assert(k >= 0);
  return 0;
}
