int is_collision(int x1, int y1, int w1, int h1, int x2, int y2, int w2, int h2) {
  if (x1 + w1 < x2) return 0;
  if (x2 + w2 < x1) return 0;
  /* if (y1 + h1 < y2) return 0; */
  if (y2 + h2 < y1) return 0;

  return 1;
}
