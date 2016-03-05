// Source: E. De Angelis, F. Fioravanti, J. A. Navas, M. Proietti:
// "Verification of Programs by Combining Iterated Specialization with
// Interpolation", HCVS 2014

#include "bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(3, x, y, flag);

  x = 1;
  y = 0;

  INIT_flag(unknown4);

  while (flag != 0) {
    PRINT_VARS();
    x = x + y;
    y = y + 1;

    if (y < 1000) {
      if (unknown4())
        flag = 1;
      else
        flag = 0;
    } else
      flag = 0;
  }
  PRINT_VARS();

  assert(x >= y);
  return 0;
}
