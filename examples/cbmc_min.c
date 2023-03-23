#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

int min(int a, int b) {
  if (a < b) {
    return a;
  } else {
    return b;
  }
}


int main() {
  int a = int_nondet();
  int b = int_nondet();

  int real = min(a, b);



  return 0;
}


