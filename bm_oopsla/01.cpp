#include "bm_oopsla.h"

int main() {
  int x = -2, y = 4;
  INITIALIZE(2, x, y);

  while(x < 0) {
    PRINT_VARS();
    int t1 = x;
    int t2 = y;
    x = t1+ t2;
    y = t1 + t2;
  }
  PRINT_VARS();

  assert(y > 0);
  return 0;
}
