#include "types-extrefs-sys.h"

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

struct extstr1 extfun4(exttyp1);  // external, invoked
struct extstr6 extfun5(exttyp6);  // external, not used
typedef struct extstr2 *pextstr2;  // typedef references extstr2
typedef exttyp2 *pexttyp2;         // typedef references exttyp2
void deffun2(struct extstr3 *p,exttyp3 q,exttypc3 r) { p->m1 = q; }  // function definition references extstr3, exttyp3, exttypc3
struct defstr1 { struct extstr4 *m1; exttyp4 *m2; };  // member declarations reference extstr4, exttyp4
extfunt1 extfun6;  // external, invoked, declared using external function typedef
exttypt7 extvar4;  // internal, references external typedef

void invoker(void) {
    deffun1(5);
    extfun1(5);
    extfun4(5);
    extfun6(5,6);
    extfun7a(1,2);
    extfun7b(3,4);
    (*deffunp1)(5);
    (*extfunp1)(5);
    extvar1 = 5;
    defvar1 = 5;
}

