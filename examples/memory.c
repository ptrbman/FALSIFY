#include "memory.h"

void mem1(int m) {
  use_mem(m - 1);
  return;
}

void mem10(int m) {
  use_mem(m - 10);
  return;
}

void use_mem(int m) {
  if (m >= 10) {
    mem10(m);
  } else if (m >= 1) {
    mem1(m);
  } else {
    return;
  }
}
