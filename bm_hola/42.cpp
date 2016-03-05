#include "bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(4, a, x, y, flag);

  x = 1;
  y = 1;

  INIT_flag(unknown);

  if (flag != 0)
    a = 0;
  else
    a = 1;

  while (unknown1()) {
    PRINT_VARS();

    if (flag != 0) {
      a = x + y;
      x++;
    } else {
      a = x + y + 1;
      y++;
    }
    if (a % 2 == 1)
      y++;
    else
      x++;
  }
  PRINT_VARS();
  // x==y

  if (flag != 0) a++;
  assert(a % 2 == 1);
}
