#include "bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(2, c, i);
  i = 0;
  c = 0;

  while (i < 1000) {
    PRINT_VARS();
    c = c + i;
    i = i + 1;
  }
  PRINT_VARS();

  assert(c >= 0);
}
