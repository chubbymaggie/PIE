#include "bm_oopsla.h"

int main(int argc, char* argv[]) {
  RECORD(9, x1, x1p, x2, x2p, x3, x3p, x4, x4p, input);

  x1 = 0;
  x2 = 0;
  x3 = 0;
  x4 = -1;

  INIT_x1p(unknown);
  INIT_x2p(unknown);
  INIT_x3p(unknown);
  INIT_x4p(unknown);
  INIT_input(unknown);

  while (input != 0) {
    PRINT_VARS();
    x1p = unknown();
    x2p = unknown();
    x3p = unknown();
    x4p = unknown();

    if (x1p <= 0 && x1p >= x4p + 1 && x2p == x3p && (x4p >= 0 || x4p <= x3p)) {
      x1 = x1p;
      x2 = x2p;
      x3 = x3p;
      x4 = x4p;
    }
    input = unknown();
  }
  PRINT_VARS();

  assert(x1 <= 0 && x1 >= x4 + 1 && x2 == x3 && (x4 >= 0 || x4 <= x3));
  return 0;
}
