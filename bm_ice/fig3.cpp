#include "bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(3, x, y, lock);

  INIT_y(unknown);
  lock = 1;
  x = y;

  if (unknown4()) {
    lock = 0;
    y = y + 1;
  }

  while (x != y) {
    PRINT_VARS();
    lock = 1;
    x = y;

    if (unknown4()) {
      lock = 0;
      y = y + 1;
    }
  }
  PRINT_VARS();

  assert(lock == 1);
}
