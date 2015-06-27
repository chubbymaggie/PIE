int xf();

void main() {
  int x = 1, y = 0;
  if(x == 1) y = 1; else y = 0;
  int z = 0;
  while(xf()) {
    x++;
    y++;
  }
  static_assert(x == y);
}
