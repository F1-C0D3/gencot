// Expression in boolean context: converted to Bool

int fbl01(int i) { return (!(i > 0))?17:4; }
int fbl02(int i) { return (!i)?17:4; }
int fbl03(int i) { return i?17:4; }
int fbl04(int i) { return (i>10?i<20:i>3)?17:4; }
int fbl05(int i) { return (i>10?i<20:i)?17:4; }
int fbl06(int i) { return (i>10?i:i>3)?17:4; }
int fbl07(int i) { return (i>10?i:i+3)?17:4; }
int fbl08(short i) { return i?17:4; }
int fbl09(long i) { return i?17:4; }

int fbl11(int i) { return (i > 0 && i < 10)?17:4; }
int fbl12(int i) { return (i && i < 10)?17:4; }
int fbl13(int i) { return (i < 10 && i)?17:4; }
int fbl14(int i) { return (i && (i+1))?17:4; }

int fbl21(int i) { return (i > 0 || i < 10)?17:4; }
int fbl22(int i) { return (i || i < 10)?17:4; }
int fbl23(int i) { return (i < 10 || i)?17:4; }
int fbl24(int i) { return (i || (i+1))?17:4; }

int fbl31(int i) { return ((i>10)==(i<20))?17:4; }
int fbl32(int i) { return (i==(i<20))?17:4; }
int fbl33(int i) { return ((i>10)==i)?17:4; }
int fbl34(int i) { return (i==i+1)?17:4; }
int fbl35(int i) { return ((i>10)!=(i<20))?17:4; }
int fbl36(int i) { return (i!=(i<20))?17:4; }
int fbl37(int i) { return ((i>10)!=i)?17:4; }
int fbl38(int i) { return (i!=i+1)?17:4; }

struct sbl { int m1,m2; };

int fbl41ln(int *p) { return p?17:4; }
int fbl41ro(int *p) { return p?17:4; }
int fbl41nn(int *p) { return p?17:4; }
int fbl41ronn(int *p) { return p?17:4; }
int fbl42ln(struct sbl *p) { return p?17:4; }
int fbl42ro(struct sbl *p) { return p?17:4; }
int fbl42nn(struct sbl *p) { return p?17:4; }
int fbl42ronn(struct sbl *p) { return p?17:4; }
int fbl43ln(int p[5]) { return p?17:4; }
int fbl43ro(int p[5]) { return p?17:4; }

// Boolean expression in non-boolean context: converted to arith

int fblctxt(int i, int j) { return i+j; }

int fbl51(int i) { return i+1; }
int fbl52(int i) { return i>0; }
int fbl53(int i) { return i+(i>0); }
int fbl54(int i) { return (i>0)>i; }
int fbl55(int i) { return -(i>0); }
int fbl56(int i) { return fbl51(i>0); }
int fbl57(int i) { return fblctxt(i>0,i); }
int fbl58(int i) { return fblctxt(i,i>0); }

int fbl61(int i) { return i>10?i<20:i>5; }
int fbl62(int i) { return i<20 && i>5; }

int fbl71(int p[5], int i) { return p[i>0]; }
void fbl72(int p[5], int i) { p[i>0] = i; }

struct sbl fbl81(struct sbl s, int i) { s.m1 = i>0; return s; }
void fbl82(struct sbl *p, int i) { p->m1 = i>0; }
