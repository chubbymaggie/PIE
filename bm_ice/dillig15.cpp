#include "bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(4, i, j, k, n);

  INIT_k(unknownu);
  INIT_n(unknownu);
  assume(k >= n && n >= 1);

  INIT_i(unknown1);

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
