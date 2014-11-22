int foo(int a, char* b){
  return b[a];
}

int main(int argc, char** argv){
  int x = foo(argc,argv[0]);
  return x;
}
