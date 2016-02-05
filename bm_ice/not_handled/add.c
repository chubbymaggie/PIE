int ADD(int i, int j)
{
  int ret;
  if(i <= 0) ret = j;
  else
    {
      int b = i - 1;
      int c = j + 1;
      ret = ADD(b, c);
    }
  return ret;
}

int main(int argc, char* argv[]) {
  RECORD(3, x, y, result);

  assert(result == x + y);
}
