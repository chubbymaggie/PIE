#include "bm_oopsla.h"

int main(int argc, char* argv[]) {
  RECORD(5, i, j, k, n, m);

  INIT_m(unknown1);
  INIT_n(unknown1);
  assume(m + 1 < n);

  INIT_i(unknown1);
  INIT_j(unknown1);
  INIT_k(unknown1);

  for (i = 0; i < n; i += 4) {
    PRINT_VARS();
    PRINT_BAR(1);

    for (j = i; j < m;) {
      PRINT_VARS();
      PRINT_BAR(2);

      if (unknown1()) {
        assert(j >= 0);
        j++;
        k = 0;
        while (k < j) {
          PRINT_VARS();
          k++;
        }
        PRINT_VARS();
        PRINT_BAR(3);
      } else {
        assert(n + j + 5 > i);
        j += 2;
      }
    }
    PRINT_VARS();
    PRINT_BAR(2);
  }
  PRINT_VARS();
  PRINT_BAR(1);

  assert(true);
  return 0;
}
