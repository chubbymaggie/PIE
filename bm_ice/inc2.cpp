#include "bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(2, x, N);

  INIT_N(unknown);
  assume(N >= 0);

  x = 0;
  while (x < N) {
    PRINT_VARS();
    x = x + 1;
  }
  PRINT_VARS();

  assert(x == N);
  return 0;
}
