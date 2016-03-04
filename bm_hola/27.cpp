#include "bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(4, i, l, k, n);

  INIT_l(unknownu);
  assume(l > 0);

  INIT_i(unknown);
  INIT_k(unknown);
  INIT_n(unknown);

  for (k = 1; k < n; k++) {
    PRINT_VARS();
    PRINT_BAR(1);

    for (i = l; i < n; i++) {
      PRINT_VARS();
    }
    PRINT_VARS();
    PRINT_BAR(2);

    for (i = l; i < n; i++) {
      PRINT_VARS();
      assert(1 <= k);
    }
    PRINT_VARS();
    PRINT_BAR(3);
  }
  PRINT_VARS();
  PRINT_BAR(1);
}
