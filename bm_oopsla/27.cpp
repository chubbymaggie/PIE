#include "bm_oopsla.h"

int main() {
  int x, y, k, i, n, j = 0, m = 0;
  INITIALIZE(7, i, j, k, m, n, x, y);

  x = unknown();
  y = unknown();
  k = unknown();
  assume((x+y) == k);

  i = unknown();
  n = unknown();

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
