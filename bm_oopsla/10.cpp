#include "bm_oopsla.h"

int main() {
  int x = -50, y;
  INITIALIZE("(%d, %d)\n", x, y);

  while(x < 0) {
    PRINT_VARS();
    x = x+y;
    y++;
  }
  PRINT_VARS();

  assert(y > 0);
  return 0;
}
