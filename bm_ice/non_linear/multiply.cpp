#include "../bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(4, j, x, y, s);

  INIT_x(unknown);
  assume(x >= 0);

  INIT_y(unknown);

  s = 0;
  j = 0;

  while (j < x) {
    PRINT_VARS();
    s = s + y;
    j++;
  }
  PRINT_VARS();

  assert(s == x * y);
}
