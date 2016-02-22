#include "bm_oopsla.h"

int main(int argc, char* argv[]) {
  RECORD(4, n, k, i, j);

  k = 0;
  i = 0;

  INIT_n(unknown);
  INIT_j(unknown);

  while (i < n) {
    PRINT_VARS();
    i = i + 1;
    k = k + 1;
  }
  PRINT_VARS();
  PRINT_BAR(1);

  j = n;
  while (j > 0) {
    PRINT_VARS();
    assert(k > 0);
    j = j - 1;
    k = k - 1;
  }
  PRINT_VARS();
  PRINT_BAR(2);

  assert(true);
  return 0;
}
