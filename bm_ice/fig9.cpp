#include "bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(2, x, y);
  x = 0;
  y = 0;

  while (y >= 0) {
    PRINT_VARS();
    y = y + x;
  }
  PRINT_VARS();

  assert(0 == 1);
}
