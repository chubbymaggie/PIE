#include "bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(3, x, m, N);

  x = 0;
  m = 0;

  INIT_N(unknown);

  while (x < N) {
    PRINT_VARS();
    if (unknown()) {
      m = x;
    }
    x = x + 1;
  }
    PRINT_VARS();

  if (N > 0) {
    assert((0 <= m) && (m < N));
  }

  return 0;
}
