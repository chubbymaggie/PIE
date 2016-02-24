#include "bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(4, i, j, k, n);

  INIT_i(unknown);
  INIT_k(unknown);
  INIT_n(unknown);
  assume(k >= n && n >= 1);

  j = 0;
  while (j <= n - 1) {
    PRINT_VARS();
    j++;
    k--;
  }
  PRINT_VARS();

  assume(j >= n);
  assert(k > -1);
  return 0;
}
