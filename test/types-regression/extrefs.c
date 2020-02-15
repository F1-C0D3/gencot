#include "extrefs.h"

void extfun1(int);  // external, invoked
void extfun2(int);  // external, listed
void extfun3(int);  // external, not used

void deffun1(int i) { } // internal, invoked

extern void (*extfunp1)(int);  // external, invoked
extern void (*extfunp2)(int);  // external, listed
extern void (*extfunp3)(int);  // external, not used

void (*deffunp1)(int) = (void*)0; // internal, invoked

extern int extvar1;  // external, used
extern int extvar2;  // external, listed
extern int extvar3;  // external, not used

int defvar1 = 1; // internal, used

void invoker(void) {
    deffun1(5);
    extfun1(5);
    (*deffunp1)(5);
    (*extfunp1)(5);
    extvar1 = 5;
    defvar1 = 5;
}
