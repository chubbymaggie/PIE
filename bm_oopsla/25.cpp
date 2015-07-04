#include "bm_oopsla.h"

int main() {
  int m, n, y, x = 0;
  INITIALIZE(4, m, n, x, y);

  assume(n >= 0);
  assume(m >= 0 && m < n);
  y = m;

  while(x < n) {
    PRINT_VARS();
    x++;
    if(x > m) y++;
  }
  PRINT_VARS();

  assert(y==n);
  return 0;
}
