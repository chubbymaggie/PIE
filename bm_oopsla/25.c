int unknown1();
int unknown2();
int unknown3();
int unknown4();

void main()
{
  int m, n;
  assume(n>=0);
  assume(m>=0);
  assume(m<n);
  int x=0;
  int y=m;
  while(x<n) {
    x++;
    if(x>m) y++;
  }
  static_assert(y==n);
}
