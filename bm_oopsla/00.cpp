#include "bm_oopsla.h"

int main(int argc, char* argv[]) {
  RECORD(2, x, y);

  x = 1; y = 1;

  while(unknown()) {
    PRINT_VARS();
    x++;
    y++;
  }
  PRINT_VARS();

  assert(x == y);
  return 0;
}
