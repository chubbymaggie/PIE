#include "bm_oopsla.h"

int main(int argc, char* argv[]) {
  RECORD(4, m, n, x, y);

  INIT_m(unknown);
  INIT_n(unknown);
  assume(n >= 0);
  assume(m >= 0);
  assume(m < n);
  y = m; x = 0;

  while(x < n) {
    PRINT_VARS();
    x++;
    if(x > m) y++;
  }
  PRINT_VARS();

  assert(y==n);
  return 0;
}
