#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

int max(int a, int b) {
  if (a > b) {
    return a;
  } else {
    return b;
  }
}


int main() {
  int a = int_nondet();
  int b = int_nondet();

  int real = max(a, b);

  assert(real >= a && real >= b && (real == a || real == b));

  return 0;
}


