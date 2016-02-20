#include "bm_oopsla.h"

int main(int argc, char* argv[]) {
  RECORD(6, a, b, c, d, x, y);

  a = 1;
  b = 1;
  c = 2;
  d = 2;
  x = 3;
  y = 3;

  while (unknown1()) {
    PRINT_VARS();
    PRINT_BAR(1);

    x = a + c;
    y = b + d;
    if ((x + y) % 2 == 0) {
      a++;
      d++;
    } else {
      a--;
    }

    while (unknown2()) {
      PRINT_VARS();
      c--;
      b--;
    }
    PRINT_VARS();
    PRINT_BAR(2);
  }
  PRINT_VARS();
  PRINT_BAR(1);

  assert(a + c == b + d);
  return 0;
}
