#include "bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(3, a, j, m);

  INIT_m(unknownu);
  assume(m > 0);

  a = 0;
  for (j = 1; j <= m; j++) {
    PRINT_VARS();
    if (unknown4())
      a++;
    else
      a--;
  }
  PRINT_VARS();

  assert(a >= 0 - m);
  assert(a <= m);
}
