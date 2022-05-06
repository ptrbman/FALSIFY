int BC = int_nondet();

int max(int a, int b) {
  if (a > b) {
    __CPROVER_assert(BC != 1, "Branch 1");
    return a;
  } else {
    __CPROVER_assert(BC != -1, "Branch -1");
    return b;
  }
}
void asd() {
  int a = int_nondet();
  int b = int_nondet();
  __CPROVER_assume(a >= b); // AUTO-GENERATED
  int ret = max(a,b);
// Facts disabled
}
void max_fact_a_smaller_than_or_equal_to_b() {
  int a = int_nondet();
  int b = int_nondet();
  __CPROVER_assume(a <= b); // AUTO-GENERATED
  int ret = max(a,b);
// Facts disabled
}
