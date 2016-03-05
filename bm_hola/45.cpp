#include "bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(9, c, d, i, j, w, x, y, z, flag);

  x = 0;
  y = 0;
  j = 0;
  i = 0;
  c = 0;
  d = 1;

  INIT_w(unknown);
  INIT_z(unknown);
  INIT_flag(unknown);

  while (unknown1()) {
    PRINT_VARS();

    x++;
    y++;
    i += x;
    j += y;
    if (flag != 0) {
      j += 1;
    }
  }
  PRINT_VARS();
  PRINT_BAR(1);

  if (j >= i)
    x = y;
  else
    x = y + 1;

  w = 1;
  z = 0;
  while (unknown2()) {
    PRINT_VARS();
    PRINT_BAR(2);

    while (unknown3()) {
      PRINT_VARS();

      if (w % 2 == 1) x++;
      if (z % 2 == 0) y++;
    }
    PRINT_VARS();
    PRINT_BAR(3);

    z = x + y;
    w = z + 1;
  }
  PRINT_VARS();
  PRINT_BAR(2);

  assert(x == y);
}
