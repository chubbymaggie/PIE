#include "bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(2, n, x);

  INIT_n(unknown);
  assume(n >= 0);

  x = 0;
  while (x < n) {
    PRINT_VARS();
    x = x + 1;
  }
  PRINT_VARS();

  assert(x == n);
}
