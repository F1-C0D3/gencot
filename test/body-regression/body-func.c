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
void ffv36(int *i, int *j) { *i = glob1; glob1 = *j; } // g1: gs1, g2: gs2

void ffv41(void) {} // ffv41: hu
void ffv42(void) {} // ffv41: hu, g: gs1
void ffv43(int *i) { *i = 5; } // i: -ar, ffv43: hu
void ffv44(int *i) { *i = 5; } // ffv44: hu
void ffv45(int *i) { glob1 = *i; } // i: -ar, g: gs1, ffv45: hu
void ffv46(int *i) { *i = glob1; } // g: gs1, ffv46: hu
void ffv47(int *i, int *j) { *i = glob1; glob1 = *j; } // ffv47: hu
void ffv48(int *i, int *j) { *i = glob1; glob1 = *j; } // g: gs1, ffv48: hu


int ffi1(void) { return 5; }

