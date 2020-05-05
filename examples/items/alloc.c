#include <stdlib.h>
#include "items.h"

int *allocInt() {
    int *res = malloc(sizeof(int));
    *res = 42;
    return res;
}

struct s *allocArr() {
    struct s *res = malloc(sizeof(struct s));
    res->arr[0] = 3;
    res->arr[1] = 9;
    res->arr[2] = 27;
} 
