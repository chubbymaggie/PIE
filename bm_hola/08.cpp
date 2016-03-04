#include "bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(2, x, y);

  x = 0;
  y = 0;

  while (unknown1()) {
    PRINT_VARS();

    if (unknown2()) {
      x++;
      y += 100;
    } else if (unknown3()) {
      if (x >= 4) {
        x++;
        y++;
      }
      if (x < 0) {
        y--;
      }
    }
  }
  PRINT_VARS();

  assert(x < 4 || y > 2);
}
