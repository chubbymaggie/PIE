#include "bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(4, x, y, n, m);

  INIT_n(unknownu);
  assume(n >= 0);

  INIT_m(unknownu);
  assume(m >= 0 && m < n);

  x = 0;
  y = m;

  while (x < n) {
    PRINT_VARS();
    x++;
    if (x >= m + 1)
      y++;
    x = x;
  }
  PRINT_VARS();

  assert(y < n + 1);
}
