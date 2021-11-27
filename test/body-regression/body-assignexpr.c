int fac1(int v) { return v=42,v; }
char fac2(char v) { return v='x',v; }
char* fac4(char* v) { return v="abc",v; }
float fac5(float v) { return v=1.5,v; }
int fav1(int v, int w) { return v=w,v; }
int fav2(int xyz_123,int w) { return xyz_123=w,xyz_123; }
int fao1(int v) { return v += 42,v; }
int fao2(int v) { return v -= 42,v; }
int fao3(int v) { return v *= 42,v; }
int fao4(int v) { return v /= 42,v; }
int fao5(int v) { return v %= 42,v; }
int fao6(int v) { return v <<= 4,v; }
int fao7(int v) { return v >>= 4,v; }
int fao8(int v) { return v &= 4,v; }
int fao9(int v) { return v |= 4,v; }
int fao10(int v) { return v ^= 4,v; }
int fao11(int v) { return v++; }
int fao12(int v) { return v--; }
int fao13(int v) { return ++v; }
int fao14(int v) { return --v; }

struct as1 { int m1, m2; };
struct as2 { int m3; struct as1 m4; };
int fas1(struct as1 s, int v) { return v = s.m1,v; }
int fas2(struct as1 s, int v) { return v = s.m1 + s.m2,v; }
int fas3(struct as2 s, int v) { return v = s.m4.m1,v; }
int fas4(struct as2 s, int v) { return v = s.m4.m1 + s.m4.m2 + s.m3,v; }
int fas5(struct as1 s) { return s.m1 = 42,s.m1; }
int fas6(struct as2 s) { return s.m4.m1 = 42,s.m4.m1; }
int fas7(struct as1 s) { return s.m1++; }
int fas8(struct as2 s) { return s.m4.m1++; }

typedef int aa1[5];
typedef struct as1 aa2[5];
int faa1(aa1 a, int v) { return v = a[3],v; }
int faa2(aa1 a, int v) { return v = a[3] + a[1],v; }
int faa3(aa1 a, int v) { return v = a[a[2]],v; }
int faa4(aa2 a, int v) { return v = a[3].m1,v; }
int faa5(aa2 a, int v) { return v = a[a[2].m2].m1,v; }
int faa6(aa1 a) { return a[3] = 42,a[3]; }
int faa7(aa2 a) { return a[3].m1 = 42,a[3].m1; }
int faa8(aa1 a) { return a[3]++; }
int faa9(aa2 a) { return a[3].m1++; }
int faa10(aa1 a) { return a[a[2]]++; }

int fam1(int v1, int v2) { return (v1 = 17) + (v2 = 4); }
int fam2(int v1, int v2) { return (v1 = 17) + (v2 = 4),v1; }
int fam3(int v1, int v2) { return (v1 = 17) + (v2 = 4),v1+v2; }
int fam4(int v1, int v2) { return v1 = (v1 = 17) + (v2 = 4),v1+v2; }
int fam5(int v1, int v2) { return (v1 = 17) + (v1 = 4); }
int fam6(int v1, int v2, int v3) { return fam1((v1 = 17), (v2 = 4)) + v3; }
int fam7(int v1, int v2, int v3) { return v3 = fam1((v1 = 17), (v2 = 4)),v1+v2+v3; }
int fam8(int v1, int v2, int v3) { return fam6((v1 = 17), (v2 = 4), (v3 = 0))+v1+v2+v3; }
int fam9(int v1, int v2, int v3) { return ((v1 = 17)?(v2 = 4):(v3 = 0))+v3; }
int fam10(int v1, int v2, int v3) { return v3 = (v1 = 17)?(v2 = 4):(v3 = 0),v1+v2+v3; }
int fam11(int v1, int v2, int v3) { return ((v1 = 17)?(v2 = 4):(v3 = 0))+v1+v2+v3; }
