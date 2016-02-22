#include "bm_oopsla.h"

int main(int argc, char* argv[]) {
  RECORD(7, x1, x1p, x2, x2p, x3, x3p, input);

  x1 = 0;
  x2 = 0;
  x3 = 0;

  INIT_x1p(unknown);
  INIT_x2p(unknown);
  INIT_x3p(unknown);
  INIT_input(unknown);

  while (input != 0) {
    PRINT_VARS();
    x1p = unknown();
    x2p = unknown();
    x3p = unknown();

    if (x1p <= x2p && (x2p >= 0 || x2p - x3p <= 2)) {
      x1 = x1p;
      x2 = x2p;
      x3 = x3p;
    }
    input = unknown();
  }
  PRINT_VARS();

  assert(x1 <= x2 && (x2 >= 0 || x2 - x3 <= 2));
  return 0;
}
