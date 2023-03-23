#include <stdio.h>
#include <stdlib.h>
#define swap(t, x, y) t z = x; x = y; y = z;

void bubble_sort(int A[], int n) {
	int i, j;

	for(i = 0; i < n; i++) {
		for(j = 0; j < n - 1; j++) {
			if(A[j] > A[j + 1]) {
				swap(int, A[j], A[j+1]);
			}
		}
	}
}

void bursted_bubble_sort(int A[], int n) {
	int i, j;
  swap(int, A[0], A[1]);
	/* for(i = 0; i < n && i < 5; i++) { */
		/* for(j = 0; j < n - 1; j++) { */
			/* if(A[j] > A[j + 1]) { */
			/* 	swap(int, A[j], A[j+1]); */
			/* } */
		/* } */
	/* } */
}


void insertion_sort(int A[], int n) {
	int i, j;
	int temp;
  
	for(i = 1; i < n; i++) {
		temp = A[i];
		j = i;
		while(j > 0 && A[j-1] > temp) {
			A[j] = A[j - 1];
			j--;
		}
		A[j] = temp;
	}
}
