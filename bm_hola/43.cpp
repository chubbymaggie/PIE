#include "bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(4, i, t, x, y);

  INIT_x(unknown);
  INIT_y(unknown);
  assume(x != y);

  i = 0;
  t = y;

  while (unknown1()) {
    PRINT_VARS();
    if (x > 0) y = y + x;
  }
  PRINT_VARS();

  assert(y >= t);
}
