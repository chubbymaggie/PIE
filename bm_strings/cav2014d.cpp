#include "bm_strings.h"

int main() {
  int i;
  string r, t;
  INITIALIZE("%d \t %s \t %s\n", i, t.c_str(), r.c_str());

  set(r, "a");
  i = len(r);

  while(unknown()) {
    PRINT_VARS();
    t = unknown_s(1);
    set(r, cat(r, t));
  }
  PRINT_VARS();

  assert(eql(sub(r, 0, i), "a"));
  return 0;
}
