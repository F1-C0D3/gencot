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
void ffv42(void) {} // ffv41: hu, g: gs1
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


void mfv11(int *i) {} // i: -ar mf (Error: Wrong result type)
void mfv12(int *i) {} // i: mf
void mfv13(int *i) { *i = 5; } // i: -ar mf (Error: Wrong result type)
void mfv14(int *i) { *i = 5; } // i: mf
void mfv15(int *i, int *j) { *i = *j; *j = 5; } // i: mf
void mfv16(int *i, int *j) { *i = *j; *j = 5; } // j: mf
void mfv17(int *i, int *j) { *i = *j; *j = 5; } // i: mf, j: mf (Ignored for j)

void mfv32(int *i) { *i = glob1; } // g: gs1, i: mf
void mfv33(int *i) { *i = glob1++; } // g: gs1 mf
void mfv34(int *i, int *j) { *i = glob1; glob1 = *j; } // j: -ar, g: gs1 mf
void mfv35(int *i, int *j) { *i = glob1; glob1 = *j; } // g: gs1 mf
void mfv36(int *i, int *j) { *i = glob1; glob2 = *j; } // g1: gs1, g2: gs2 mf
void mfv37(int *i, int *j) { *i = glob1; glob1 = *j; } // j: -ar, g: gs1, i: mf
void mfv38(int *i, int *j) { *i = glob1; glob1 = *j; } // g: gs1, j: mf

void mfv44(int *i) { *i = 5; } // mfv44: hu, i: mf
void mfv45(int *i) { glob1 = *i; } // i: -ar, g: gs1 mf, mfv45: hu
void mfv46(int *i) { *i = glob1; } // g: gs1 mf, mfv46: hu
void mfv47(int *i, int *j) { *i = glob1; glob1 = *j; } // mfv47: hu, i: mf
void mfv48(int *i, int *j) { *i = glob1; glob1 = *j; } // g: gs1, mfv48: hu, j: mf

int *mfi11(int *i) { return i; } // i: -ar mf
int *mfi12(int *i) { return i; } // i: mf
int *mfi15(int *i, int *j) { *i = *j; *j = 5; return j; } // i: -ar, j: -ar mf 
int *mfi16(int *i, int *j) { *i = *j; *j = 5; return i; } // j: -ar, i: mf
int *mfi17(int *i, int *j) { *i = *j; *j = 5; return i; } // i: -ar mf
int *mfi18(int *i, int *j) { *i = *j; *j = 5; return j; } // j: mf

int *mfi31(int *i) { glob1 = *i; return i; } // i: -ar, g: gs1 mf
int *mfi32(int *i) { *i = glob1; return i; } // g: gs1, i: mf
int mfi33(int *i) { *i = glob1++; return glob1; } // g: gs1 mf
int mfi34(int *i, int *j) { *i = glob1; glob1 = *j; return glob1; } // j: -ar, g: -ar gs1 mf
int mfi35(int *i, int *j) { *i = glob1; glob1 = *j; return glob1; } // g: gs1, i: mf
int mfi36(int *i, int *j) { *i = glob1; glob1 = *j; return glob2; } // g1: gs1, g2: gs2 mf

int *mfi43(int *i) { *i = 5; return i; } // i: -ar mf, mfv43: hu
int mfi44(int *i) { *i = 5; return 2; } // mfv44: hu, i: mf
int mfi45(int *i) { glob1 = *i; return 2; } // i: -ar, g: gs1 mf, mfv45: hu
int mfi46(int *i) { *i = glob1; return 2; } // g: gs1, mfv46: hu, i: mf
int mfi47(int *i, int *j) { *i = glob1; glob1 = *j; return 2; } // g: gs1, mfv47: hu, i: mf
int mfi48(int *i, int *j) { *i = glob1; glob1 = *j; return 2; } // g: gs1, mfv48: hu, j: mf

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

void cmfv11(int *i) { mfv11(i); }
void cmfv12(int *i) { mfv12(i); }
void cmfv15(int *i, int *j) { mfv15(i,j); }
void cmfv16(int *i, int *j) { mfv16(i,j); }
void cmfv17(int *i, int *j) { mfv17(i,j); }

void cmfv32(int *i) { mfv32(i); } // g: gs1
void cmfv33(int *i) { mfv33(i); } // g: gs1
void cmfv34(int *i, int *j) { mfv34(i,j); } // g: gs1
void cmfv35(int *i, int *j) { mfv35(i,j); } // g: gs1
void cmfv36(int *i, int *j) { mfv36(i,j); } // g1: gs1, g2: gs2
void cmfv37(int *i, int *j) { mfv37(i,j); } // g: gs1
void cmfv38(int *i, int *j) { mfv38(i,j); } // g: gs1

void cmfv44(int *i) { mfv44(i); } // cmfv44: hu
void cmfv45(int *i) { mfv45(i); } // g: gs1, cmfv45: hu
void cmfv46(int *i) { mfv46(i); } // g: gs1, cmfv46: hu
void cmfv47(int *i, int *j) { mfv47(i,j); } // cmfv47: hu
void cmfv48(int *i, int *j) { mfv48(i,j); } // g: gs1, cmfv48: hu

int *cmfi11(int *i) { return mfi11(i); }
int *cmfi12(int *i) { return mfi12(i); }
int *cmfi15(int *i, int *j) { return mfi15(i,j); }
int *cmfi16(int *i, int *j) { return mfi16(i,j); }
int *cmfi17(int *i, int *j) { return mfi17(i,j); }
int *cmfi18(int *i, int *j) { return mfi18(i,j); }

int *cmfi31(int *i) { return mfi31(i); } // g: gs1
int *cmfi32(int *i) { return mfi32(i); } // g: gs1
int cmfi33(int *i) { return mfi33(i); } // g: gs1
int cmfi34(int *i, int *j) { return mfi34(i,j); } // g: gs1
int cmfi35(int *i, int *j) { return mfi35(i,j); } // g: gs1
int cmfi36(int *i, int *j) { return mfi36(i,j); } // g1: gs1, g2: gs2

int *cmfi43(int *i) { return mfi43(i); } // cmfv43: hu
int cmfi44(int *i) { return mfi44(i); } // cmfv44: hu
int cmfi45(int *i) { return mfi45(i); } // g: gs1, cmfv45: hu
int cmfi46(int *i) { return mfi46(i); } // g: gs1, cmfv46: hu
int cmfi47(int *i, int *j) { return mfi47(i,j); } // g: gs1, cmfv47: hu
int cmfi48(int *i, int *j) { return mfi48(i,j); } // g: gs1, cmfv48: hu

