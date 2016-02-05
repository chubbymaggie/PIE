#include "bm_oopsla.h"

int main(int argc, char* argv[]) {
  RECORD(7, flag, t, s, a, b, x, y);

  INIT_flag(unknown4);
  t = 0; s = 0; a = 0; b = 0;

  while(unknown1()){
    PRINT_VARS();
    a++;
    b++;
    s += a;
    t += b;
    if (flag != 0) {
      t += a;
    }
  }
  PRINT_VARS();
  //2s >= t
  x = 1;
  if (flag != 0) {
    x = t - 2 * s + 2;
  }
  //x <= 2
  y = 0;
  PRINT_BAR();
  while(y <= x) {
    PRINT_VARS();
    if (unknown2()) {
      y++;
    }
    else {
      y += 2;
    }
  }
  PRINT_VARS();
  assert(y <= 4);
  return 0;
}

