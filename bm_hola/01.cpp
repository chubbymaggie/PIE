#include "bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(2, x, y);

  x = 1;
  y = 1;

  while (unknown1()) {
    PRINT_VARS();
    int t1 = x;
    int t2 = y;
    x = t1 + t2;
    y = t1 + t2;
  }
  PRINT_VARS();

  assert(y >= 1);
}
