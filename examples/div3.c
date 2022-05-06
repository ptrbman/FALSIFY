int div3(int c) {
  if ((c & 15) % 3 == 0) {
    return 1;
  } else {
    return 0;
  }
}
