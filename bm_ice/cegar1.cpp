#include "bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(3, x, y, input);

  INIT_x(unknown0to2);
  assume(0 <= x && x <= 2);

  INIT_y(unknown0to2);
  assume(0 <= y && y <= 2);

  INIT_input(unknown1);

  while (input != 0) {
    PRINT_VARS();
    x = x + 2;
    y = y + 2;
    input = unknown1();
  }
  PRINT_VARS();

  assert(!((x == 4) && (y == 0)));
  return 0;
}
