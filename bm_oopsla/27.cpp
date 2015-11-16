#include "bm_oopsla.h"

int main(int argc, char* argv[]) {
  RECORD(7, i, j, k, m, n, x, y);

  INIT_x(unknown);
  INIT_y(unknown);
  INIT_k(unknown);
  assume((x+y) == k);

  j = 0; m = 0;
  INIT_i(unknown);
  INIT_n(unknown);

  while(j < n) {
    PRINT_VARS();
    if(j==i) {
      x++;
      y--;
    } else {
      y++;
      x--;
    }

    if(unknown4()) m = j;
    j++;
  }
  PRINT_VARS();

  assert((x+y) == k);
  if(n > 0) {
    assert(0 <= m);
    assert(m < n);
  }
  return 0;
}
