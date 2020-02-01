struct { int m11; int m12; } *var_pstruct1,*var_pstruct2;
struct str1 { int m11; int m12; } *var_pstr1;
struct str2 { int m11; int m12; } *var_pstr2;
union  { int m11; int m12; } *var_punion1,*var_punion2;
union uni1 { int m11; int m12; } *var_puni1;
union uni2 { int m11; int m12; } *var_puni2;
int *var_pint1,*var_pint2;
enum { CP01, CP02, } *var_penum1,*var_penum2;
enum enm1 { CP11, CP12, } *var_penm1;
enum enm2 { CP21, CP22, } *var_penm2;
int **var_ppint1,**var_ppint2;
int (*var_p2arr51)[5],(*var_p2arr52)[5];
void *var_pvoid1,*var_pvoid2;

int (*pf1)(int p1);
int (*pf2)(int p1, short p2);
int (*pf3)(void);
void (*pfv1)(int p1);
void (*pfv2)(int p1, short p2);
void (*pfv3)(void);
void (*pfvv1)(int p1, ...);
void (*pfvv2)(int p1, short p2, ...);
void (*pfvr1)(const char *p1);
void (*pfvr2)(int p1, const char *p2);
void (*pfvl1)(char *p1);
void (*pfvl2)(char *p1, char *p2);
int (*pfl1)(char *p1);
int (*pfl2)(char *p1, char *p2);
int (*pfl3)(int p1, char *p2);
int (*pfl4)(char *p1, char *p2, int p3);

void fpp1(char *p1) { }
void *fpp2(void) {}
void *fpp3(void) {}
void *(*pfvr3)(void);
void *(*pfvr4)(void);

struct str3 { int *m21; int *m22; } var_struct1;
struct { int *m; } var_struct2;

typedef int *pt1;
pt1 pt1vr;

typedef int *pt2;
pt2 pt2vr;

typedef int t1;
t1 *t1vr1;
int *t1vr2;

typedef struct str4 { int m31; int m32; } str4_t, *pstr4_t;
struct str1 *var_pstr12;
struct str4 *var_pstr4;
str4_t *var_pstr4_t;
pstr4_t var_pstr42_t;

typedef struct str5 { int m31; int m32; } str5_t, *pstr5_t;
struct str5 *var_pstr5;
str5_t *var_pstr5_t;
pstr5_t var_pstr52_t;
