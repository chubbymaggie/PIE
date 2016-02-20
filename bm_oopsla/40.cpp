#include "bm_oopsla.h"

int main(int argc, char* argv[]) {
  RECORD(10, a, b, c, d, j, w, x, y, z, flag);

  a = 0;
  b = 0;
  x = 0;
  y = 0;
  z = 0;
  j = 0;
  w = 0;

  INIT_flag(unknown4);

  while (unknown1()) {
    PRINT_VARS();
    PRINT_BAR(1);

    int i = z;
    int j = w;
    int k = 0;
    while (i < j) {
      PRINT_VARS();
      k++;
      i++;
    }
    PRINT_VARS();
    PRINT_BAR(2);

    x = z;
    y = k;

    if (x % 2 == 1) {
      x++;
      y--;
    }

    while (unknown2()) {
      PRINT_VARS();
      if (x % 2 == 0) {
        x += 2;
        y -= 2;
      } else {
        x--;
        y--;
      }
    }
    PRINT_VARS();
    PRINT_BAR(3);

    z++;
    w = x + y + 1;
  }
  PRINT_VARS();
  PRINT_BAR(1);

  c = 0;
  d = 0;
  while (unknown3()) {
    PRINT_VARS();

    c++;
    d++;
    if (flag != 0) {
      a++;
      b++;
    } else {
      a += c;
      b += d;
    }
  }
  PRINT_VARS();
  PRINT_BAR(4);

  assert(w >= z && a - b == 0);
  return 0;
}
