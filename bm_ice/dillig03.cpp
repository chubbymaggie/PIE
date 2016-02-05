#include "bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(2, k, w);

  k = 1;
  w = 1;

  while (unknown1()) {
    PRINT_VARS();
    if (unknown()) w++;
    k += w;
  }
  PRINT_VARS();

  assert(k > 0);
}
