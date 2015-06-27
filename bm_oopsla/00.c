int unknown();

void main() {
  int x = 1, y = 1;
  while(unknown()) {
    x++;
    y++;
  }
  static_assert(x == y);
}
