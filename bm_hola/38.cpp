#include "bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(4, i, n, x, y);

  x = 0;
  y = 0;
  i = 0;
  INIT_n(unknown);

  while (i < n) {
    PRINT_VARS();
    i++;
    x++;
    if (i % 2 == 0) y++;
  }
  PRINT_VARS();

  if (i % 2 == 0) assert(x == 2 * y);
}
