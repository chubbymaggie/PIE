#include "bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(4, m, n, x, y);

  INIT_m(unknownu);
  INIT_n(unknownu);
  assume(n >= 0);
  assume(m >= 0);
  assume(m < n);

  x = 0;
  y = m;

  while (x < n) {
    PRINT_VARS();

    x++;
    if (x > m) y++;
  }
  PRINT_VARS();

  assert(y == n);
}
