#include "bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(5, i, j, x, y, flag);

  j = 0;
  i = 0;
  x = 0;
  y = 0;

  INIT_flag(unknown);

  while (unknown1()) {
    PRINT_VARS();
    x++;
    y++;
    i += x;
    j += y;
    if (flag != 0) j += 1;
  }
  PRINT_VARS();

  assert(j >= i);
}
