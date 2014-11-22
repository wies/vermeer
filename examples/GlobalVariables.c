//A simple recursive adder
int glob = 3;
unsigned moreGlobals;
int *pt1 = &glob;
int *pt2;
char a[2][3];

int main(int argc, char** argv){
  a[1][2] = 'b';
  pt2 = &glob;
  *pt2 = 12;
  int a = 2 + moreGlobals;
  int b = glob;
}
