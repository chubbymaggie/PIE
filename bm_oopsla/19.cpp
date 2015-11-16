#include "bm_oopsla.h"

int main(int argc, char* argv[]) {
  RECORD(3, i, j, n);

  INIT_n(unknown);
  i = 0; j = 1;

  while(i < n){
    PRINT_VARS();
    if(j % 2 == 1) i++;
    if(i % 2 == 1) j++;
  }
  PRINT_VARS();

  assert(j >= i);
  return 0;
}
