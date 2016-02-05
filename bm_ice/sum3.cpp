#include "bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(3, x, n1, sn, loop1);

  x = 0;
  sn = 0;

  INIT_n1(unknownu);
  INIT_loop1(unknownu);

  while(1){
    sn = sn + 1;
    x++;
    __VERIFIER_assert(sn==x*1 || sn == 0);
  }
}
