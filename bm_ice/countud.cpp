#include "bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(3, n, x, y);

  INIT_n(unknown);
  assume(n >= 0); // unsigned

  x = n;
  y = 0;

  while (x > 0) {
    PRINT_VARS();
    x--;
    y++;
  }
  PRINT_VARS();

  assert(y == n);
}
