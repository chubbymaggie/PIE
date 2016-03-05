#include "bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(6, i, j, k, n, z, flag);

  INIT_n(unknownu);
  assume(n >= 0);

  INIT_z(unknown);
  INIT_flag(unknown);

  k = 1;
  if (flag != 0) {
    INIT_k(unknownu);
    assume(k >= 0);
  }
  i = 0;
  j = 0;

  while (i <= n) {
    PRINT_VARS();
    i++;
    j += i;
  }
  PRINT_VARS();

  z = k + i + j;
  assert(z > 2 * n);
}
