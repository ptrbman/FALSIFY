#include "stack.h"

int stack[STACK_SIZE];
int stack_ptr = 0;

int pop(int *elem) {
  if (stack_ptr == 0) {
    return 1;
  } else {
    stack_ptr -= 1;
    *elem = stack[stack_ptr];
    return 0;
  }
}

int push(int elem) {
  if (stack_ptr < STACK_SIZE) {
    stack[stack_ptr] = elem;
    stack_ptr += 1;
    return 0;
  } else {
    return 1;
  }
}
