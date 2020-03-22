typedef int (*fun_t)(char *p1);

struct s1 { int i; fun_t f[5][2]; };

struct s2 { int j; fun_t g; int (*gg)(char* p1); };

extern struct s1 str1;
extern struct s2 str2;
extern fun_t h1;
extern int h2(char*,...);
extern int h3(char*);
extern int h4(char*);

int fid(char *p1) {
    return h1(p1) + 5;
}
void fpvr1(char *p1) {}
void fpvr2(int p1, char *p2) {}
void fpvl1(char *p1) {}
void fpvl2(char *p1, char *p2) {
    h2(p1,p2);
    h3(p2);
    h3(p1);
}
int fpl1(char *p1) { return 0; }
int fpl2(char *p1, char *p2) { return 0; }
int fpl3(int p1, char *p2) { return 0; }
int fpl4(char *p1, char *p2, int p3) { return h2(p2); }
void fpvd1(char *p1) {}
void fpvd2(char *p1, char *p2) {
    str1.f[3][1](p1);
    str2.g(p1);
    (*str2.g)(p2);
    str2.gg(p2);
    (*h1)(p1);
}
int fpd1(char *p1) { return 0; }
int fpd2(char *p1, char *p2) { return 0; }
char *fpr1(char *p1) { return 0; }
char *fpr2(char *p1, char *p2) { return 0; }

void (*pfpvr1)(char *p1);
void (*pfpvr2)(int p1, char *p2);
void (*pfpvl1)(char *p1);
void (*pfpvl2)(char *p1, char *p2);
int (*pfpl1)(char *p1);
int (*pfpl2)(char *p1, char *p2);
int (*pfpl3)(int p1, char *p2);
int (*pfpl4)(char *p1, char *p2, int p3);
void (*pfpvd1)(char *p1);
void (*pfpvd2)(char *p1, char *p2);
int (*pfpd1)(char *p1);
int (*pfpd2)(char *p1, char *p2);
char *(*pfpr1)(char *p1);
char *(*pfpr2)(char *p1, char *p2);

struct pmd {
void (*pmfpvr1)(char *p1);
void (*pmfpvr2)(int p1, char *p2);
void (*pmfpvl1)(char *p1);
void (*pmfpvl2)(char *p1, char *p2);
int (*pmfpl1)(char *p1);
int (*pmfpl2)(char *p1, char *p2);
int (*pmfpl3)(int p1, char *p2);
int (*pmfpl4)(char *p1, char *p2, int p3);
void (*pmfpvd1)(char *p1);
void (*pmfpvd2)(char *p1, char *p2);
int (*pmfpd1)(char *p1);
int (*pmfpd2)(char *p1, char *p2);
char *(*pmfpr1)(char *p1);
char *(*pmfpr2)(char *p1, char *p2);
};
