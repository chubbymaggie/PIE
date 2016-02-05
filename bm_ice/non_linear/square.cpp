#include "../bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(3, n, r, x);

  n = 0;
  x = 0;

  INIT_r(unknown);
  while (r != 0) {
    PRINT_VARS();
    n++;
    x += 2 * n - 1;
    r = unknown();
  }
  PRINT_VARS();

  assert(x == n * n);
}
