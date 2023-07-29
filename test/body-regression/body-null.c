#include <stddef.h>

int *fn1(int i, int *p) { return i?p:NULL; }
int *fn2(int i, int *p) { return i?p:NULL; } // p: nn

