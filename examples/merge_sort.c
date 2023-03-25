void merge(int t[], int s1[], int n1, int s2[], int n2) {
  int i = 0; int j = 0;
  while (i<n1 || j<n2) {
    if (i >= n1) { t[i+j] = s2[j]; j++; }
    else if (j >= n2) { t[i+j] = s1[i]; i++; }
    else if (s1[i] <= s2[j]) { t[i+j] = s1[i]; i++; }
    else if (s1[i] >= s2[j]) { t[i+j] = s2[j]; j++; }
  }
  return;
}

void merge_sort(int A[], int n) {
  if (n == 1) {
    return;
  } else {
    int n1, n2;
    if (n % 2 == 0) { n1 = n/2; n2 = n/2; }
    else { n1 = n/2 + 1; n2 = n/2; }
    int tmp1[n1];
    for (int i = 0; i<n1; i++) tmp1[i] = A[i];
    int tmp2[n2];
    for (int i = 0; i<n2; i++) tmp2[i] = A[n1 + i];
    merge_sort(tmp1, n1);
    merge_sort(tmp2, n2);

    merge(A, tmp1, n1, tmp2, n2);
    return;
  }
}
