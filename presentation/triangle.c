// Adapted from:
// Introduction to Software Testing
// Authors: Paul Ammann & Jeff Offutt
// Chapter 6; page ??
// See TriangleTypeTest.java for JUnit tests

const int INVALID = 0;
const int EQUILATERAL = 1;
const int ISOSCELES = 2;
const int SCALENE = 3;

int triangle(int s1, int s2, int s3)
{
  // Reject non-positive sides
  if (s1 <= 0 || s2 <= 0 || s3 <= 0) {
    return INVALID;
  } else {
    // 
  }

  // Check triangle inequality
  if (s1+s2 <= s3 || s2+s3 <= s1 || s1+s3 <= s2) {
    return INVALID;
  } else {
    //
  }

  // Identify equilateral triangles
  if ((s1 == s2) && (s2 == s3)) {
    return EQUILATERAL;
  } else {
    //
  }

  // Identify isosceles triangles
  if ((s1 == s2) || (s2 == s3) || (s1 == s3)) {
    return ISOSCELES;
  } else {
    //
  }

  return SCALENE;
}
