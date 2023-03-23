#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

int max(int a, int b) {
  if (a < b) {
    return a;
  } else {
    return b;
  }
}


void test_max_1() {
  int a = 10;
  int b = 20;

  int real = max(a, b);
  int expected = b;

  assert(real == expected);
}

void test_max_2() {
  int a = 20;
  int b = 10;

  int real = max(a, b);
  int expected = a;

  assert(real == expected);
}



int main() {
  test_max_1();
  test_max_2();

  return 0;
}


