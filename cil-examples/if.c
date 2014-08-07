int main(int argc, char** argv){
  int a = 1;
  int b = 0;
  int d = 1;
  int c;
  if (a) {
    if (b) {
      c = 1;
    } else {
      c = 2;
    }
  } else {
    c = 3;
  }
  
  int w = 12;

   d = c ? 2 : 3;
  if (a)
    b = 10;
  else
    b = 11;
  if(d)
    c = 10;
  return c;
}
