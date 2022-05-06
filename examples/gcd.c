#include <stdio.h>

int gcd(int a, int b) {
  int x, y, z;
  x = a;
  y = b;
  z = b;
  while (z != 0) {
    z = x % y;
    y = z;
    x = y;
  }
  return x;
}

int main(int argc, char* argv[]) {
  int g = gcd(10, 5);
  printf("%d\n", g);
}
