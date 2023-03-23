int sum(int* list, int len) {
  int s = 0;
  for (int i=0; i<len; i++)
    s += list[i];

  return s;
}


