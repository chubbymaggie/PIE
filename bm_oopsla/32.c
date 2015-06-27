int main() {
  int i, j;
  int x = i;
  int y = j;
  while(x!=0) {
    x--;
    y--;
  }
  if(i==j)
    static_assert(y==0);
}
