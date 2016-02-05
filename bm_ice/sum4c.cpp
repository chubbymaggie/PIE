#include "bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(3, i, sn, SIZE);

  i = 1;
  sn = 0;
  INIT_SIZE(unknown);

  while (i <= SIZE) {
    PRINT_VARS();
    sn = sn + 1;
    i++;
  }
  PRINT_VARS();

  assert(sn == SIZE || sn == 0);
}
