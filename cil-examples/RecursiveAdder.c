//A simple recursive adder

int adder(int x, int y)
{
  if(x > 0) return adder(x-1, y+1);
  else if(x < 0) return -1* adder(-x,-y);
  else return y;
}

int main(int argc, char** argv){
  int a = 2;
  int b = 3;
  return adder(a, b);
}
