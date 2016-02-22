#include "bm_oopsla.h"

int main(int argc, char* argv[]) {
  RECORD(7, c, d, k, x, y, z, input);

  INIT_c(unknown);
  INIT_d(unknown);
  INIT_k(unknown);
  INIT_x(unknown);
  INIT_y(unknown);
  INIT_input(unknown);

  z = 1;
  while (z < k) {
    PRINT_VARS();
    z = 2 * z;
  }
  PRINT_VARS();
  PRINT_BAR(1);

  assert(z >= 1);

  while (x > 0 && y > 0) {
    PRINT_VARS();
    c = unknown();
    if (c != 0) {
      x = x - d;
      y = unknown();
      z = z - 1;
    } else {
      y = y - d;
    }
  }
  PRINT_VARS();
  PRINT_BAR(2);

  assert(true);
}
