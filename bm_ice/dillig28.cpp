#include "bm_oopsla.h"

int main(int argc, char* argv[]) {
  RECORD(3, n, x, y);

  x = 0;
  y = 0;
  n = 0;

  while (unknown1()) {
    PRINT_VARS();
    x++;
    y++;
  }
  PRINT_VARS();
  PRINT_BAR(1);

  while (x <= n - 1 || x >= n + 1) {
    PRINT_VARS();
    x--;
    y--;
  }
  PRINT_VARS();
  PRINT_BAR(2);

  assert(x != n || y == n);
  return 0;
}
