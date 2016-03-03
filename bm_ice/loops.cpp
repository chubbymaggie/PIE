#include "bm_oopsla.h"

int main(int argc, char* argv[])
{
  RECORD(3, s, x, y);

  INIT_x(unknownu);
  assume(x >= 0);

  INIT_y(unknown);

  s = 0;
  while (s < x) {
    PRINT_VARS();
    s++;
  }
  PRINT_VARS();
  PRINT_BAR(1);

  y = 0;
  while (y < s) {
    PRINT_VARS();
    y++;
  }
  PRINT_VARS();
  PRINT_BAR(2);

  assert(x == y);
}
