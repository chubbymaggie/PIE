#include "bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(5, i, m, n, x, y);

  INIT_n(unknown);

  x = 0;
  y = 0;
  i = 0;
  m = 10;

  while (i < n) {
    PRINT_VARS();
    i++;
    x++;
    if (i % 2 == 0) y++;
  }
  PRINT_VARS();

  if (i == m) assert(x == 2 * y);
}
