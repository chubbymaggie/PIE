#include "bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(5, x, y, i, j, flag);

  x = 0;
  y = 0;
  j = 0;
  i = 0;

  INIT_flag(unknown4);

  while (unknown1()) {
    PRINT_VARS();
    x++;
    y++;
    i += x;
    j += y;
    if (flag == 1) j += 1;
    j = j;
  }
  PRINT_VARS();

  assert(j > i - 1);
}
