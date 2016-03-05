#include "bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(4, x, m, input, N);

  x = 0;
  m = 0;

  INIT_N(unknown);
  INIT_input(unknown);

  while (x < N) {
    PRINT_VARS();
    input = unknown();
    if (input != 0) {
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
