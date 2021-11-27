int fc1(void) { return 42; }
char fc2(void) { return 'x'; }
char fc3(void) { return 'xx'; }
char* fc4(void) { return "abc"; }
float fc5(void) { return 1.5; }
int fv1(int v) { return v; }
int fv2(int xyz_123) { return xyz_123; }
int fo1(void) { return +42; }
int fo2(void) { return -42; }
int fo3(void) { return !42; }
int fo4(void) { return ~42; }
int fo5(void) { return 17 + 4; }
int fo6(void) { return 17 - 4; }
int fo7(void) { return 17 * 4; }
int fo8(void) { return 17 % 4; }
int fo9(void) { return 17 / 4; }
int fo10(void) { return 17 << 4; }
int fo11(void) { return 17 >> 4; }
int fo12(void) { return 17 < 4; }
int fo13(void) { return 17 > 4; }
int fo14(void) { return 17 <= 4; }
int fo15(void) { return 17 >= 4; }
int fo16(void) { return 17 == 4; }
int fo17(void) { return 17 != 4; }
int fo18(void) { return 17 & 4; }
int fo19(void) { return 17 | 4; }
int fo20(void) { return 17 ^ 4; }
int fo21(void) { return 17 && 4; }
int fo22(void) { return 17 || 4; }
int f1(void) { return 17?4:42; }
int f2(void) { return 17,4,42; }
int f3(void) { return fc1(); }
int f4(void) { return fv1(42); }
int fx(int a, char b, int c) { return a; }
int f5(void) { return fx(17,'x',4); }

struct s1 { int m1, m2; };
struct s2 { int m3; struct s1 m4; };
int fs1(struct s1 s) { return s.m1; }
int fs2(struct s1 s) { return s.m1 + s.m2; }
int fs3(struct s2 s) { return s.m4.m1; }
int fs4(struct s2 s) { return s.m4.m1 + s.m4.m2 + s.m3; }

typedef int a1[5];
typedef struct s1 a2[5];
int fa1(a1 a) { return a[3]; }
int fa2(a1 a) { return a[3] + a[1]; }
int fa3(a1 a) { return a[a[2]]; }
int fa4(a2 a) { return a[3].m1; }
int fa5(a2 a) { return a[a[2].m2].m1; }
