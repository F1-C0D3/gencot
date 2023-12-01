typedef struct { int m11; int m12; } snam1;
typedef struct nstr2 { int m11; int m12; } snam2;
snam1 var_snam1;
snam2 var_snam2;
snam1 *var_psnam1;
snam2 *var_psnam2;
struct snam { snam1 m_snam1; snam1 *m_psnam1; snam2 m_snam2; snam2 *m_psnam2; };
void f_snam(snam1 p_snam1, snam1 *p_psnam1, snam2 p_snam2, snam2 *p_psnam2) {}
snam1 var_asnam1[5];
snam2 var_asnam2[5];
snam1 *var_apsnam1[5];
snam2 *var_apsnam2[5];

typedef int fnam1(int p1);
fnam1 var_fnam1;
fnam1 *var_pfnam1;
struct fnam { fnam1 *m_pfnam1; };
void f_fnam(fnam1 p_fnam1, fnam1 *p_pfnam1) {}
fnam1 *var_apfnam1[5];

typedef int (*fpnam1)(int p1);
fpnam1 var_fpnam1;
fpnam1 *var_pfpnam1;
struct fpnam { fpnam1 m_fpnam1; fpnam1 *m_pfpnam1; };
void f_fpnam(fpnam1 p_fpnam1, fpnam1 *p_pfpnam1) {}
fpnam1 var_afpnam1[5];

typedef int anam1[5];
anam1 var_anam1;
anam1 *var_panam1;
struct anam { anam1 m_anam1; anam1 *m_panam1; };
void f_anam(anam1 p_anam1, anam1 *p_panam1) {}
anam1 var_aanam1[5];

typedef int inam1;
inam1 var_inam1;
inam1 *var_pinam1;
struct inam { inam1 m_inam1; inam1 *m_pinam1; };
void f_inam(inam1 p_inam1, inam1 *p_pinam1) {}
inam1 var_ainam1[5];

typedef int fnam2(inam1 p1); // should be equivalent with fnam1
typedef int (*fpnam2)(inam1 p1); // should be equivalent with fpnam1
typedef int fnam3(snam2 p1, fnam1 p2, anam1 p3);
typedef int fnam4(snam2 p1, fnam2 p2, int p3[5]); // should be equivalent with fnam3
typedef int fnam5(struct nstr2 p1, int p2(int), anam1 p3); // should be equivalent with fnam3
typedef int (*fpnam3)(snam2 p1, fnam1 p2, anam1 p3);
typedef int (*fpnam4)(snam2 p1, fnam2 p2, int p3[5]); // should be equivalent with fpnam3
typedef int (*fpnam5)(struct nstr2 p1, int p2(int), anam1 p3); // should be equivalent with fpnam3

typedef void vnam;
