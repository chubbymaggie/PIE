// Source: A. Costan, S. Gaubert, E. Goubault, M. Martel, S. Putot: "A Policy
// Iteration Algorithm for Computing Fixed Points in Static Analysis of
// Programs", CAV 2005

#include "bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(2, i, j);

  i = 1;
  j = 10;

  while (j >= i) {
    PRINT_VARS();
    i = i + 2;
    j = j - 1;
  }
  PRINT_VARS();

  assert(j == 6);
  return 0;
}
