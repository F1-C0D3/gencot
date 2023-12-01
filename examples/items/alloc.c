#include <stdlib.h>
#include "items.h"

int *allocInt() {
    int *res = malloc(sizeof(int));
    *res = 'x';
    return res;
}

struct s *allocArr() {
    struct s *res = malloc(sizeof(struct s));
    res->arr[0] = 'a';
    res->arr[1] = 'b';
    res->arr[2] = 'c';
} 
