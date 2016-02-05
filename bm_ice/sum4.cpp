#include "bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(2, i, sn);

  i = 1;
  sn = 0;

  while (i <= 8) {
    PRINT_VARS();
    sn = sn + 1;
    i++;
  }
  PRINT_VARS();

  assert(sn == 8 || sn == 0);
  return 0;
}
