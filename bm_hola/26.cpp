#include "bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(4, w, x, y, z);

  w = 1;
  z = 0;
  x = 0;
  y = 0;

  while (unknown1()) {
    PRINT_VARS();

    while (unknown2()) {
      PRINT_VARS();
      if (w % 2 == 1) x++;
      if (z % 2 == 0) y++;
    }
    PRINT_VARS();
    PRINT_BAR(2);

    while (unknown1()) {
      PRINT_VARS();
      z = x + y;
      w = z + 1;
    }
    PRINT_VARS();
    PRINT_BAR(3);
  }
  PRINT_VARS();
  PRINT_BAR(1);

  assert(x == y);
}
