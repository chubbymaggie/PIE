#include "bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(3, i, n, sn);

  i = 1;
  sn = 0;
  INIT_n(unknown);

  while (i <= n) {
    PRINT_VARS();
    sn = sn + 1;
    i++;
  }
  PRINT_VARS();

  assert(sn == n || sn == 0);
}
