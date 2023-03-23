#include <limits.h>

int abs(int v) {
  // we want to find the absolute value of v
  unsigned int r;  // the result goes here 
  int const mask = v >> sizeof(int) * CHAR_BIT - 1;

  r = (v + mask) ^ mask;
  return r;
}
