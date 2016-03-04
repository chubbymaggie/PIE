#include "bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(4, a, b, i, n);

  INIT_n(unknownu);
  assume(n >= 0);

  a = 0;
  b = 0;
  i = 0;

  while (i < n) {
    PRINT_VARS();

    if (unknown1()) {
      a = a + 1;
      b = b + 2;
    } else {
      a = a + 2;
      b = b + 1;
    }
    i = i + 1;
  }
  PRINT_VARS();

  assert(a + b == 3 * n);
}
