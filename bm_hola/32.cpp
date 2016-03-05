#include "bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(5, b, i, j, k, n);

  INIT_b(unknown);
  INIT_j(unknown);

  i = j;
  k = 100;
  for (n = 0; n < 2 * k; n++) {
    PRINT_VARS();
    if (b != 0) {
      i++;
      b = 0;
    } else {
      j++;
      b = 1;
    }
  }
  PRINT_VARS();

  assert(i == j);
}
