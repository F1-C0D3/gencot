// Function definitions

void ffv1(void) {}
void ffv2(void) { return; }

void ffv11(int *i) {} // i: -ar
void ffv12(int *i) {}
void ffv13(int *i) { *i = 5; } // i: -ar
void ffv14(int *i) { *i = 5; }
void ffv15(int *i, int *j) { *i = *j; *j = 5; } // i: -ar, j: -ar
void ffv16(int *i, int *j) { *i = *j; *j = 5; } // j: -ar
void ffv17(int *i, int *j) { *i = *j; *j = 5; } // i: -ar
void ffv18(int *i, int *j) { *i = *j; *j = 5; }

int glob1; // glob1: gs1
int glob2; // glob2: gs2

void ffv21(void) {} // g: gs1
void ffv22(void) {} // g: gs2
void ffv23(void) {} // g1: gs1, g2: gs2
void ffv24(void) {} // g2: gs2, g1: gs1
void ffv25(void) { glob1 = 5; } // g: gs1
void ffv26(void) { glob2 = 5; } // g: gs1 (!)
void ffv27(void) { glob1++; } // g: gs1
void ffv28(void) { glob1 = glob2; } // g1: gs1, g2: gs2

void ffv31(int *i) { glob1 = *i; } // i: -ar, g: gs1
void ffv32(int *i) { *i = glob1; } // g: gs1
void ffv33(int *i) { *i = glob1++; } // g: gs1
void ffv34(int *i, int *j) { *i = glob1; glob1 = *j; } // j: -ar, g: gs1
void ffv35(int *i, int *j) { *i = glob1; glob1 = *j; } // g: gs1
void ffv36(int *i, int *j) { *i = glob1; glob2 = *j; } // g1: gs1, g2: gs2

void ffv41(void) {} // ffv41: hu
void ffv42(void) {} // ffv42: hu, g: gs1
void ffv43(int *i) { *i = 5; } // i: -ar, ffv43: hu
void ffv44(int *i) { *i = 5; } // ffv44: hu
void ffv45(int *i) { glob1 = *i; } // i: -ar, g: gs1, ffv45: hu
void ffv46(int *i) { *i = glob1; } // g: gs1, ffv46: hu
void ffv47(int *i, int *j) { *i = glob1; glob1 = *j; } // ffv47: hu
void ffv48(int *i, int *j) { *i = glob1; glob1 = *j; } // g: gs1, ffv48: hu


int ffi1(void) { return 5; }

int ffi11(int *i) { return 5; } // i: -ar
int ffi12(int *i) { return 5; }
int ffi13(int *i) { *i = 5; return 2; } // i: -ar 
int ffi14(int *i) { *i = 5; return 2; }
int ffi15(int *i, int *j) { *i = *j; *j = 5; return 2; } // i: -ar, j: -ar 
int ffi16(int *i, int *j) { *i = *j; *j = 5; return 2; } // j: -ar
int ffi17(int *i, int *j) { *i = *j; *j = 5; return 2; } // i: -ar
int ffi18(int *i, int *j) { *i = *j; *j = 5; return 2; }

int ffi21(void) { return 5; } // g: gs1
int ffi22(void) { return 5; } // g: gs2
int ffi23(void) { return 5; } // g1: gs1, g2: gs2
int ffi24(void) { return 5; } // g2: gs2, g1: gs1
int ffi25(void) { glob1 = 5; return 2; } // g: gs1
int ffi26(void) { glob2 = 5; return 2; } // g: gs1 (!)
int ffi27(void) { glob1++; return 2; } // g: gs1
int ffi28(void) { glob1 = glob2; return 2; } // g1: gs1, g2: gs2

int ffi31(int *i) { glob1 = *i; return 2; } // i: -ar, g: gs1
int ffi32(int *i) { *i = glob1; return 2; } // g: gs1
int ffi33(int *i) { *i = glob1++; return 2; } // g: gs1
int ffi34(int *i, int *j) { *i = glob1; glob1 = *j; return 2; } // j: -ar, g: gs1
int ffi35(int *i, int *j) { *i = glob1; glob1 = *j; return 2; } // g: gs1
int ffi36(int *i, int *j) { *i = glob2; glob1 = *j; return 2; } // g1: gs1, g2: gs2

int ffi41(void) { return 5; } // ffv41: hu
int ffi42(void) { return 5; } // ffv41: hu, g: gs1
int ffi43(int *i) { *i = 5; return 2; } // i: -ar, ffv43: hu
int ffi44(int *i) { *i = 5; return 2; } // ffv44: hu
int ffi45(int *i) { glob1 = *i; return 2; } // i: -ar, g: gs1, ffv45: hu
int ffi46(int *i) { *i = glob1; return 2; } // g: gs1, ffv46: hu
int ffi47(int *i, int *j) { *i = glob1; glob1 = *j; return 2; } // ffv47: hu (Error: no parameter for glob1)
int ffi48(int *i, int *j) { *i = glob1; glob1 = *j; return 2; } // g: gs1, ffv48: hu
int ffi49(int *i, int *j) { *i = *j; return 2; } // g: gs1, ffv49: hu


// Function calls

void cffv1(void) { ffv1(); }

void cffv11(int *i) { ffv11(i); }
void cffv12(int *i) { ffv12(i); }
void cffv15(int *i, int *j) { ffv15(i,j); }
void cffv16(int *i, int *j) { ffv16(i,j); }
void cffv17(int *i, int *j) { ffv17(i,j); }
void cffv18(int *i, int *j) { ffv18(i,j); }

void cffv21(void) { ffv21(); } // g: gs1
void cffv22(void) { ffv22(); } // g: gs1 (Error: no argument for gs2)
void cffv23(void) { ffv23(); } // g1: gs1, g2: gs2

void cffv31(int *i) { ffv31(i); } // g: gs1
void cffv32(int *i) { ffv32(i); } // g: gs1
void cffv34(int *i, int *j) { ffv34(i,j); } // g: gs1
void cffv35(int *i, int *j) { ffv35(i,j); } // g: gs1
void cffv36(int *i, int *j) { ffv36(i,j); } // g1: gs1, g2: gs2

void cffv41(void) { ffv41(); } // cffv41: hu
void cffv42(void) { ffv42(); } // cffv41: hu, g: gs1
void cffv43(int *i) { ffv43(i); } // cffv43: hu
void cffv44(int *i) { ffv44(i); } // cffv44: hu
void cffv45(int *i) { ffv45(i); } // g: gs1, cffv45: hu
void cffv46(int *i) { ffv46(i); } // g: gs1, cffv46: hu
void cffv47(int *i, int *j) { ffv47(i,j); } // cffv47: hu
void cffv48(int *i, int *j) { ffv48(i,j); } // g: gs1, cffv48: hu

int cffi1(void) { return ffi1(); }

int cffi11(int *i) { return ffi11(i); }
int cffi12(int *i) { return ffi12(i); }
int cffi15(int *i, int *j) { return ffi15(i,j); }
int cffi16(int *i, int *j) { return ffi16(i,j); }
int cffi17(int *i, int *j) { return ffi17(i,j); }
int cffi18(int *i, int *j) { return ffi18(i,j); }

int cffi21(void) { return ffi21(); } // g: gs1
int cffi22(void) { return ffi22(); } // g: gs2
int cffi23(void) { return ffi23(); } // g1: gs1, g2: gs2

int cffi31(int *i) { return ffi31(i); } // g: gs1
int cffi32(int *i) { return ffi32(i); } // g: gs1
int cffi34(int *i, int *j) { return ffi34(i,j); } // g: gs1
int cffi35(int *i, int *j) { return ffi35(i,j); } // g: gs1
int cffi36(int *i, int *j) { return ffi36(i,j); } // g1: gs1, g2: gs2

int cffi41(void) { return ffi41(); } // cffv41: hu
int cffi42(void) { return ffi42(); } // cffv41: hu, g: gs1
int cffi43(int *i) { return ffi43(i); } // cffv43: hu
int cffi44(int *i) { return ffi44(i); } // cffv44: hu
int cffi45(int *i) { return ffi45(i); } // g: gs1, cffv45: hu
int cffi46(int *i) { return ffi46(i); } // heap: gs1, cffv46: hu
int cffi48(int *i, int *j) { return ffi48(i,j); } // g: gs1, cffv48: hu
int cffi49(int *i, int *j) { return ffi49(i,j); } // g: gs1, cffv49: hu

// Function Pointers

typedef void (*fpfvv) (void), ffvv (void);
typedef void (*fpfvi) (int*), ffvi (int*);
typedef int (*fpfiv) (void),  ffiv (void);
typedef int (*fpfii) (int*),  ffii (int*);

struct fstd { fpfvv fvv; fpfvi fvi; fpfiv fiv; fpfii fii; };
struct fsptd { ffvv *fvv; ffvi *fvi; ffiv *fiv; ffii *fii; };
struct fsdir { void (*fvv)(void); void (*fvi)(int*); int (*fiv)(void); int (*fii)(int*); };
struct fsro { fpfvi fvi; fpfii fii; }; // fvi/1: ro, fii/1: ro

fpfvv ffp1vv(struct fstd s) { return s.fvv; }
fpfvi ffp1vi(struct fstd s) { return s.fvi; }
fpfiv ffp1iv(struct fstd s) { return s.fiv; }
fpfii ffp1ii(struct fstd s) { return s.fii; }

void cfpv1(struct fstd s) { s.fvv(); }
void cfpv2(struct fstd s) { (*s.fvv)(); }
void cfpv3(struct fsptd s) { s.fvv(); }
void cfpv4(struct fsdir s) { s.fvv(); }
void cfpv5(fpfvv a[5]) { a[1](); }
void cfpv6(fpfvv a[5]) { (*a[1])(); }
void cfpv7(struct fstd s) { ffp1vv(s)(); }
void cfpv8(struct fstd s) { (*ffp1vv(s))(); }
void cfpv9(fpfvv f) { f(); }

void cfpv11(struct fstd s, int *i) { s.fvi(i); }
void cfpv12(struct fsptd s, int *i) { s.fvi(i); }
void cfpv13(struct fsdir s, int *i) { s.fvi(i); }
void cfpv14(struct fsro s, int *i) { s.fvi(i); }
void cfpv15(fpfvi a[5], int *i) { a[1](i); }
void cfpv16(struct fstd s, int *i) { ffp1vi(s)(i); }
void cfpv17(fpfvi f, int *i) { f(i); }
void cfpv18(ffvi f, int *i) { f(i); }

int cfpi1(struct fstd s) { return s.fiv(); }
int cfpi2(struct fstd s) { return (*s.fiv)(); }
int cfpi3(struct fsptd s) { return s.fiv(); }
int cfpi4(struct fsdir s) { return s.fiv(); }
int cfpi5(fpfiv a[5]) { return a[1](); }
int cfpi6(fpfiv a[5]) { return (*a[1])(); }
int cfpi7(struct fstd s) { return ffp1iv(s)(); }
int cfpi8(struct fstd s) { return (*ffp1iv(s))(); }
int cfpi9(fpfiv f) { return f(); }

int cfpi11(struct fstd s, int *i) { return s.fii(i); }
int cfpi12(struct fsptd s, int *i) { return s.fii(i); }
int cfpi13(struct fsdir s, int *i) { return s.fii(i); }
int cfpi14(struct fsro s, int *i) { return s.fii(i); }
int cfpi15(fpfii a[5], int *i) { return a[1](i); }
int cfpi16(struct fstd s, int *i) { return ffp1ii(s)(i); }
int cfpi17(fpfii f, int *i) { return f(i); }
int cfpi18(ffii f, int *i) { return f(i); }
