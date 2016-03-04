#include "bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(6, i, j, k, n, t, pvlen);

  k = 0;
  i = 0;

  INIT_j(unknown);
  INIT_n(unknown);
  INIT_t(unknown);
  INIT_pvlen(unknown);

  //  pkt = pktq->tqh_first;
  while (unknown1()) {
    PRINT_VARS();
    i = i + 1;
  }
  PRINT_VARS();
  PRINT_BAR(1);

  if (i > pvlen) {
    pvlen = i;
  } else {
  }
  i = 0;

  while (unknown2()) {
    PRINT_VARS();
    t = i;
    i = i + 1;
    k = k + 1;
  }
  PRINT_VARS();
  PRINT_BAR(2);

  while (unknown3()) {
    PRINT_VARS();
  }
  PRINT_VARS();
  PRINT_BAR(3);

  j = 0;
  n = i;

  assert(k >= 0);
  k = k - 1;
  i = i - 1;
  j = j + 1;
  while (j < n) {
    PRINT_VARS();
    assert(k >= 0);
    k = k - 1;
    i = i - 1;
    j = j + 1;
  }
  PRINT_VARS();
  PRINT_BAR(4);
}
