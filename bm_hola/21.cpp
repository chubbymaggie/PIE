#include "bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(7, c1, c2, i, j, k, n, v);

  INIT_n(unknownu);
  assume(n > 0);
  assume(n < 10);

  INIT_j(unknown);
  INIT_v(unknown);

  c1 = 4000;
  c2 = 2000;

  k = 0;
  i = 0;
  while (i < n) {
    PRINT_VARS();
    i++;
    if (unknown4())
      v = 0;
    else
      v = 1;

    if (v == 0)
      k += c1;
    else
      k += c2;
  }
  PRINT_VARS();

  assert(k > n);
}
