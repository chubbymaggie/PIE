#include "bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(8, x1, x2, x3, d1, d2, d3, c1, c2);

  INIT_x1(unknown);
  INIT_x2(unknown);
  INIT_x3(unknown);

  assume(x1 >= 0 && x2 >= 0 && x3 >= 0);

  d1 = 1;
  d2 = 1;
  d3 = 1;

  INIT_c1(unknown4);
  INIT_c2(unknown4);

  while (x1 > 0 && x2 > 0 && x3 > 0) {
    PRINT_VARS();
    if (c1 == 1)
      x1 = x1 - d1;
    else if (c2 == 1)
      x2 = x2 - d2;
    else
      x3 = x3 - d3;

    c1 = unknown4();
    c2 = unknown4();
  }
  PRINT_VARS();

  assert(x1 == 0 || x2 == 0 || x3 == 0);
  return 0;
}
