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

struct extstr1 extfun4(exttyp1);
struct extstr6 extfun5(exttyp6);
typedef struct extstr2 *pextstr2;
typedef exttyp2 *pexttyp2;
void deffun2(struct extstr3 *p,exttyp3 q,exttypc3 r) { p->m1 = q; }
struct defstr1 { struct extstr4 *m1; exttyp4 *m2; };

void invoker(void) {
    deffun1(5);
    extfun1(5);
    extfun4(5);
    (*deffunp1)(5);
    (*extfunp1)(5);
    extvar1 = 5;
    defvar1 = 5;
}

