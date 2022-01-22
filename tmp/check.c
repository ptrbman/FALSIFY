int max(int a, int b) {
  if (a > b) {
    return a;
  } else {
    return b;
  }
}
void max_fact_0() {
  int a = 0;
  int b = 1;
  int ret = max(a,b);
  assert(ret == 1); // AUTO-GENERATED
}