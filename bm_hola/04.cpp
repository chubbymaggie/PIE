#include "bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(2, x, y);

  INIT_y(unknown);
  x = -50;

  while (x < 0) {
    PRINT_VARS();
    x = x + y;
    y++;
  }
  PRINT_VARS();

  assert(y > 0);
}
