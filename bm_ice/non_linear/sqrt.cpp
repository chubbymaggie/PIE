#include "../bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(4, n, a, su, t);

  INIT_n(unknown);
  assume(n >= 0);

  // a = 0, su = 1, t = 1, n = 26
  // a = 1, su = 4, t = 3
  // a = 2, t = 5, su = 9,
  // a = 3, t = 7, su = 16
  // a = 4, t = 9, su = 25,
  // a = 5, t = 11, su = 36, n = 26

  a = 0;
  su = 1;
  t = 1;

  // Finds "t*t + 2t - 4su = const", "2a*n - t*n + n = const", "2a*su - t*su +
  // su = const"
  // Finds "a + a*t + t - 2su = const", "a*a + t - su = const", "2a*t + t - t*t
  // = const"
  while (su <= n) {
    PRINT_VARS();
    a = a + 1;
    t = t + 2;
    su = su + t;
  }
  PRINT_VARS();

  assert((a * a <= n) && ((a + 1) * (a + 1) > n));
}
