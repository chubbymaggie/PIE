#include "bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(3, i, n, sum);

  INIT_n(unknownu);
  assume(n >= 0);

  INIT_i(unknown);
  sum = 0;
  for (i = 0; i < n; ++i) {
    PRINT_VARS();
    sum = sum + i;
  }
  PRINT_VARS();

  assert(sum >= 0);
}
