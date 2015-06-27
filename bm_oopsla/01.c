int unknown1();

void main()
{
 int x = -2, y = 4;
 while(x < 0) {
   int t1 = x;
   int t2 = y;
   x = t1+ t2;
   y = t1 + t2;
 }
 static_assert(y > 0);
}

