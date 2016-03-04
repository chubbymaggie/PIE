#include "bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(4, w, x, y, z);

  w = 1;
  z = 0;
  x = 0;
  y = 0;

  while (unknown2()) {
    PRINT_VARS();

    if (w == 1) {
      x++;
      w = 0;
    };
    if (z == 0) {
      y++;
      z = 0;
    };
  }
  PRINT_VARS();

  assert(x == y);
}
