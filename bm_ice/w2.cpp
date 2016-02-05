#include "bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(3, n, x, input);

  INIT_input(unknown);
  INIT_n(unknown);
  assume(n > 0);

  x = 0;
  while (0 == 0) {
    if (input) {

      x = x + 1;
      if (x >= n) {
        break;
      }
    }
    input = __VERIFIER_nondet_int();
  }

  assert(x == n);
}
