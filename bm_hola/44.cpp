#include "bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(5, i, j, k, n, flag)

  i = 0;
  j = 0;

  INIT_k(unknown);
  INIT_flag(unknown4);

  if (flag == 1) {
    n = 1;
  } else {
    n = 2;
  }

  i = 0;

  while (i <= k) {
    PRINT_VARS();
    i++;
    j = j + n;
  }
  PRINT_VARS();

  if (flag == 1) assert(j == i);
}
