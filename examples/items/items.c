#include <stdio.h>
#include "items.h"

int1P_t allocInt(void);
struct s *allocArr(void);

static void printAlloc(intCP_t p1, const struct s *p2) {
    puts("p1 points to"); putchar(*p1);
    puts("\np2 contains:"); putchar(p2->arr[0]); putchar(p2->arr[1]); putchar(p2->arr[2]); putchar('\n');
}

int main() {
  puts("Items example");
  printAlloc(allocInt(),allocArr());
}


