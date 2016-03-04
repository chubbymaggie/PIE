#include "bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(3, j, k, flag);

  j = 2;
  k = 0;
  INIT_flag(unknown);

  while (unknown1()) {
  PRINT_VARS();
    if (flag != 0)
      j = j + 4;
    else {
      j = j + 2;
      k = k + 1;
    }
  }
  PRINT_VARS();

  if (k != 0) assert(j == 2 * k + 2);
}
