// Source: E. De Angelis, F. Fioravanti, J. A. Navas, M. Proietti:
// "Verification of Programs by Combining Iterated Specialization with
// Interpolation", HCVS 2014

#include "bm_oopsla.h"

int main(int argc, char* argv[]) {
  RECORD(2, x, y);

  x = 1;
  y = 0;

  while (unknown4()) {
    PRINT_VARS();
    x = x + y;
    y = y + 1;
  }
  PRINT_VARS();

  assert(x >= y);
  return 0;
}
