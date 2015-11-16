#include "bm_oopsla.h"

int main(int argc, char* argv[]) {
  RECORD(2, x, y);

  x = -2; y = 4;

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
