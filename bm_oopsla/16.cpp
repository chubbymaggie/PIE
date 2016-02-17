#include "bm_oopsla.h"

int main(int argc, char* argv[]) {
  RECORD(3, x, y, n);

  x = 0; y = 0; n = 0;

  PRINT_BAR(1);
  while(unknown()) {
    PRINT_VARS();
    x++;
    y++;
  }
  PRINT_VARS();
  
  PRINT_BAR(2);
  while(x != n) {
    PRINT_VARS();
    x--;
    y--;
  }
  PRINT_VARS();
  
  assert(y == n);
  return 0;
}
