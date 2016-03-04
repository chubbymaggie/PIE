#include "bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(7, i, j, k, m, n, x, y);

  INIT_k(unknown);
  INIT_x(unknown);
  INIT_y(unknown);
  assume((x + y) == k);

  INIT_i(unknown);
  INIT_n(unknown);

  m = 0;
  j = 0;
  while (j < n) {
    PRINT_VARS();
    if (j == i) {
      x++;
      y--;
    } else {
      y++;
      x--;
    }
    if (unknown1()) m = j;
    j++;
  }
  PRINT_VARS();

  assert((x + y) == k);
  if (n > 0) {
    assert(0 <= m);
    assert(m < n);
  }
}
