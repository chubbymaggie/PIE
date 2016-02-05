#include "bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(3, j, k, n);

  INIT_n(unknown1);
  assume(k >= n && n >= 1);

  j = 0;
  while (j <= n - 1) {
    PRINT_VARS();
    j++;
    k--;
  }
  PRINT_VARS();

  assert(k > 0);
  return 0;
}
