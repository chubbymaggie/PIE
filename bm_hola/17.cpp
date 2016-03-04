#include "bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(4, i, j, k, n);

  INIT_n(unknownu);
  assume(n > 0);

  k = 1;
  i = 1;
  j = 0;

  while (i < n) {
    PRINT_VARS();
    PRINT_BAR(1);

    j = 0;
    while (j < i) {
      PRINT_VARS();

      k += (i - j);
      j++;
    }
    PRINT_VARS();
    PRINT_BAR(2);

    i++;
  }
  PRINT_VARS();
  PRINT_BAR(1);

  assert(k >= n);
}
