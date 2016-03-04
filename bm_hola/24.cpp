#include "bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(4, i, j, k, n);

  INIT_n(unknown);

  for (i = 0; i < n; i++) {
    PRINT_VARS();
    PRINT_BAR(1);

    for (j = i; j < n; j++) {
      PRINT_VARS();
      PRINT_BAR(2);

      for (k = j; k < n; k++) {
        PRINT_VARS();

        assert(k >= i);
      }
      PRINT_VARS();
      PRINT_BAR(3);
    }
    PRINT_VARS();
    PRINT_BAR(2);
  }
  PRINT_VARS();
  PRINT_BAR(1);
}
