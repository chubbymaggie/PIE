#include "bm_oopsla.h"

int main(int argc, char* argv[]) {
  RECORD(4, k, x, y, z);

  INIT_k(unknown1);

  z = k;
  x = 0;
  y = 0;

  while (unknown1()) {
    PRINT_VARS();
    PRINT_BAR(1);

    int c = 0;
    while (unknown2()) {
      PRINT_VARS();

      if (z == k + y - c) {
        x++;
        y++;
        c++;
      } else {
        x++;
        y--;
        c++;
      }
    }
    PRINT_VARS();
    PRINT_BAR(2);

    while (unknown3()) {
      PRINT_VARS();
      x--;
      y--;
    }
    PRINT_VARS();
    PRINT_BAR(3);

    z = k + y;
  }
  PRINT_VARS();
  PRINT_BAR(1);

  assert(x == y);
  return 0;
}
