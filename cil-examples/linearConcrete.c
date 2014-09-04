int main(int argc, char** argv)
{
  int x_1_1 = 2;
  int x_2_1 = 1;
  int x_1_2 = x_1_1 + x_2_1;
  int x_3_1 = x_1_2 > 4;
  assert(x_1_2 > 2);
  assert(x_2_1);
  return x_1_2;
}
