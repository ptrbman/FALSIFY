

void bubble() {
  int len = 7;
  int a[len];

  for (int i=1; i<len; i++)
    a[i] = int_nondet();

  for (int i=0; i<len; i++) {
    for (int j=i; j<len; j++) {
      if (a[i] > a[j]) {
        int tmp = a[i];
        a[i] = a[j];
        a[j] = a[i];
      }
    }
  }

  for (int i=1; i<len; i++)
    __CPROVER_assert(a[i-1] <= a[i], "test");
}
