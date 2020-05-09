#include <stdio.h>
#include "items.h"

intP_t allocInt(void);
struct s *allocArr(void);

static void printAlloc(intCP_t p1, intCA_t p2) {
    printf("p1 points to %d\n",*p1);
    printf("p2 contains: %d, %d, %d\n", p2[0], p2[1], p2[2]);
}

int main(int argc, const char *argv[]) {
  printf("Items example\n");
  printAlloc(allocInt(),allocArr()->arr);
}


