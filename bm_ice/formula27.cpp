#include "bm_oopsla.h"

int main(int argc, char* argv[]) {
  RECORD(11, x1, x1p, x2, x2p, x3, x3p, x4, x4p, x5, x5p, input);

  x1 = 0;
  x2 = 0;
  x3 = 0;
  x4 = 0;
  x5 = 0;

  INIT_x1p(unknown);
  INIT_x2p(unknown);
  INIT_x3p(unknown);
  INIT_x4p(unknown);
  INIT_x5p(unknown);
  INIT_input(unknown);

  while (input != 0) {
    PRINT_VARS();

    x1p = unknown();
    x2p = unknown();
    x3p = unknown();
    x4p = unknown();
    x5p = unknown();

    if (0 <= x1p && x1p <= x4p + 1 && x2p == x3p && (x2p <= -1 || x4p <= x2p + 2) && x5p == 0) {
      x1 = x1p;
      x2 = x2p;
      x3 = x3p;
      x4 = x4p;
      x5 = x5p;
    }

    input = unknown();
  }
  PRINT_VARS();

  assert(0 <= x1 && x1 <= x4 + 1 && x2 == x3 && (x2 <= -1 || x4 <= x2 + 2) && x5 == 0);
  return 0;
}
