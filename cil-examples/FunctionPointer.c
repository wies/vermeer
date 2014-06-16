//A simple recursive adder
int global_var = 1;

int adder(int x, int y)
{
  if(x > 0) return adder(x-1, y+1);
  else if(x < 0) return -1* adder(-x,-y);
  else return y;
}

int foo(int c, int d)
{
  return adder(c,d);
}

int main(int argc, char** argv){
  int a = 2;
  int b = 2 + global_var;
  int (*f)(int,int) = adder;
  int x =  f(a, b);
  int y = foo(a,b);
  return x + y;
}
