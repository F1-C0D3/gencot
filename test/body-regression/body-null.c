#include <stddef.h>

// Using NULL in condition branch
int *fn1(int i, int *p) { return i?p:NULL; }
int *fn2(int i, int *p) { return i?p:NULL; } // p: nn

// Functions used as context:
int fcnl(int *i) { return 0; }
int fcnn(int *i) { return 0; }
// Global variables used as context:
int *globcnl;
int *globcnn;

// global not-null probes:
int *globnn; // global const-val variable
int *frnn(void); // (external) function with not-null result

// global null probes:
int *globnl; // global const-val variable
int *frnl(void); // (external) function with null result

// struct probes:
struct nns1 { int mrg; int *mnn; int *mnl; };
struct nns2 { struct nns1 *snl; struct nns1 *snn; };

// array probes:
typedef int nna1[5];  // regular elements
typedef int* nna2[5]; // not-null elements
typedef int* nna3[5]; // null elements
typedef nna1 nna4[5];   // null array elements
typedef nna1 nna5[5];   // not-null array elements

// Using values of not-null type (can be converted to MayNull).

// Direct use of probe in context
int fn11nl(int *pnn) { return fcnl(pnn); }
int fn11nn(int *pnn) { return fcnn(pnn); }
int fn12nl(void) { return fcnl(globnn); }
int fn12nn(void) { return fcnn(globnn); }
int fn13nl(void) { return fcnl(frnn()); }
int fn13nn(void) { return fcnn(frnn()); }
int fn14nl(int *pnn, int *qnn, int i) { return fcnl(i?pnn:qnn); }
int fn14nn(int *pnn, int *qnn, int i) { return fcnn(i?pnn:qnn); }

// Probe assigned to variable
void fn21nl(void) { globcnl = frnn(); }
void fn21nn(void) { globcnn = frnn(); }
void fn22nl(int *pnl) { pnl = frnn(); }
int fn22nn(int *pnn) { pnn = frnn(); return *pnn; }

// Probe returned as result
int *fn31nl(void) { return frnn(); }
int *fn31nn(void) { return frnn(); }

// Probe used in conditional expression with other branch as context
int fn41nl(int *pnn, int *qnl, int i) { return fcnn(i?pnn:qnl); }
int fn42nl(int *pnl, int *qnn, int i) { return fcnn(i?pnl:qnn); }

// Probe is a struct component
int *fn51nl(struct nns1 *pnn) { return pnn->mnn; }
int *fn51nn(struct nns1 *pnn) { return pnn->mnn; }
int fn52nl(struct nns1 *pnn) { return fcnl(pnn->mnn); }
int fn52nn(struct nns1 *pnn) { return fcnn(pnn->mnn); }
void fn53nl(struct nns1 *pnn) { globcnl = pnn->mnn; }
void fn53nn(struct nns1 *pnn) { globcnn = pnn->mnn; }
void fn54nl(struct nns1 *pnn, int *pnl) { pnl = pnn->mnn; }
int fn54nn(struct nns1 *pnn, int *qnn) { qnn = pnn->mnn; return *qnn; }
int fn55nl(struct nns1 *pnn, int *qnl, int i) { return fcnn(i?pnn->mnn:qnl); }
int fn55nn(struct nns1 *pnn, int *qnn, int i) { return fcnn(i?pnn->mnn:qnn); }

// Probe used by accessing a struct component or pointer deref
int fn61nn(struct nns1 *pnn) { return pnn->mrg; }
int fn62nn(struct nns2 *pnn) { return pnn->snn->mrg; }
int fn63nn(void) { return *globnn; }
int fn64nn(void) { return *frnn(); }

// Probe is an array element
int *fn71nl(nna2 pnn) { return pnn[1]; }
int *fn71nn(nna2 pnn) { return pnn[1]; }
int fn72nl(nna2 pnn) { return fcnl(pnn[1]); }
int fn72nn(nna2 pnn) { return fcnn(pnn[1]); }
void fn73nl(nna2 pnn) { globcnl = pnn[1]; }
void fn73nn(nna2 pnn) { globcnn = pnn[1]; }
void fn74nl(nna2 pnn, int *pnl) { pnl = pnn[1]; }
int fn74nn(nna2 pnn, int *qnn) { qnn = pnn[1]; return *qnn; }
int fn75nl(nna2 pnn, int *qnl, int i) { return fcnn(i?pnn[1]:qnl); }
int fn75nn(nna2 pnn, int *qnn, int i) { return fcnn(i?pnn[1]:qnn); }

// Probe used by accessing an array element
int fn81nn(nna1 pnn) { return pnn[1]; }
int fn82nn(nna5 pnn) { return pnn[1][1]; }

// Probe assigned to struct component or array element
void fn91nl(struct nns1 *pnn) { pnn->mnl = frnn(); }
void fn91nn(struct nns1 *pnn) { pnn->mnn = frnn(); }
void fn92nl(nna3 pnl) { pnl[1] = frnn(); }
void fn92nn(nna2 pnl) { pnl[1] = frnn(); }

// Using MayNull values (cannot be converted to not-null)

// Direct use of probe in context
int gn11nl(int *pnl) { return fcnl(pnl); }
int gn11nn(int *pnl) { return fcnn(pnl); }
int gn12nl(void) { return fcnl(globnl); }
int gn12nn(void) { return fcnn(globnl); }
int gn13nl(void) { return fcnl(frnl()); }
int gn13nn(void) { return fcnn(frnl()); }
int gn14nl(int *pnl, int *qnl, int i) { return fcnl(i?pnl:qnl); }
int gn14nn(int *pnl, int *qnl, int i) { return fcnn(i?pnl:qnl); }

// Probe assigned to variable
void gn21nl(void) { globcnl = frnl(); }
void gn21nn(void) { globcnn = frnl(); }
void gn22nl(int *pnl) { pnl = frnl(); }
int gn22nn(int *pnn) { pnn = frnl(); return *pnn; }

// Probe returned as result
int *gn31nl(void) { return frnl(); }
int *gn31nn(void) { return frnl(); }

// Probe is a struct component
int *gn51nl(struct nns1 *pnn) { return pnn->mnl; }
int *gn51nn(struct nns1 *pnn) { return pnn->mnl; }
int gn52nl(struct nns1 *pnn) { return fcnl(pnn->mnl); }
int gn52nn(struct nns1 *pnn) { return fcnn(pnn->mnl); }
void gn53nl(struct nns1 *pnn) { globcnl = pnn->mnl; }
void gn53nn(struct nns1 *pnn) { globcnn = pnn->mnl; }
void gn54nl(struct nns1 *pnn, int *pnl) { pnl = pnn->mnl; }
int gn54nn(struct nns1 *pnn, int *qnn) { qnn = pnn->mnl; return *qnn; }
int gn55nl(struct nns1 *pnn, int *qnl, int i) { return fcnn(i?pnn->mnl:qnl); }
int gn55nn(struct nns1 *pnn, int *qnn, int i) { return fcnn(i?pnn->mnl:qnn); }

// Probe used by accessing a struct component or pointer deref
int gn61nl(struct nns1 *pnl) { return pnl->mrg; }
int gn62nl(struct nns2 *pnn) { return pnn->snl->mrg; }
int gn63nl(void) { return *globnl; }
int gn64nl(void) { return *frnl(); }

// Probe is an array element
int *gn71nl(nna3 pnn) { return pnn[1]; }
int *gn71nn(nna3 pnn) { return pnn[1]; }
int gn72nl(nna3 pnn) { return fcnl(pnn[1]); }
int gn72nn(nna3 pnn) { return fcnn(pnn[1]); }
void gn73nl(nna3 pnn) { globcnl = pnn[1]; }
void gn73nn(nna3 pnn) { globcnn = pnn[1]; }
void gn74nl(nna3 pnn, int *pnl) { pnl = pnn[1]; }
int gn74nn(nna3 pnn, int *qnn) { qnn = pnn[1]; return *qnn; }
int gn75nl(nna3 pnn, int *qnl, int i) { return fcnn(i?pnn[1]:qnl); }
int gn75nn(nna3 pnn, int *qnn, int i) { return fcnn(i?pnn[1]:qnn); }

// Probe used by accessing an array element
int gn81nl(nna1 pnl) { return pnl[1]; }
int gn82nl(nna4 pnn) { return pnn[1][1]; }

// Probe assigned to struct component or array element
void gn91nl(struct nns1 *pnn) { pnn->mnl = frnl(); }
void gn91nn(struct nns1 *pnn) { pnn->mnn = frnl(); }
void gn92nl(nna3 pnl) { pnl[1] = frnl(); }
void gn92nn(nna2 pnl) { pnl[1] = frnl(); }

// Using MayNull values after NULL-test in expression.

// Direct use of probe in context
int tn11nl(int *pnl) { return pnl?fcnl(pnl):0; }
int tn11nn(int *pnl) { return pnl?fcnn(pnl):0; }
int tn12nl(void) { return globnl?fcnl(globnl):0; }
int tn12nn(void) { return globnl?fcnn(globnl):0; }
int tn13nl(void) { return frnl()?fcnl(frnl()):0; }
int tn13nn(void) { return frnl()?fcnn(frnl()):0; }
int tn14nl(int *pnl, int *qnn, int i) { return pnl?fcnl(i?pnl:qnn):0; }
int tn14nn(int *pnl, int *qnn, int i) { return pnl?fcnn(i?pnl:qnn):0; }

// Probe assigned to variable
void tn21nl(int *qnl, int *qnn) { globcnl = qnl?qnl:qnn; }
void tn21nn(int *qnl, int *qnn) { globcnn = qnl?qnl:qnn; }
void tn22nl(int *pnl, int *qnl, int *qnn) { pnl = qnl?qnl:qnn; }
int tn22nn(int *pnn, int *qnl, int *qnn) { pnn = qnl?qnl:qnn; return *pnn; }

// Probe returned as result
int *tn31nl(int *qnl, int *qnn) { return qnl?qnl:qnn; }
int *tn31nn(int *qnl, int *qnn) { return qnl?qnl:qnn; }

// Probe is a struct component
int *tn51nl(struct nns1 *pnn) { return pnn->mnl?pnn->mnl:pnn->mnn; }
int *tn51nn(struct nns1 *pnn) { return pnn->mnl?pnn->mnl:pnn->mnn; }
int tn52nl(struct nns1 *pnn) { return fcnl(pnn->mnl?pnn->mnl:pnn->mnn); }
int tn52nn(struct nns1 *pnn) { return fcnn(pnn->mnl?pnn->mnl:pnn->mnn); }
void tn53nl(struct nns1 *pnn) { globcnl = pnn->mnl?pnn->mnl:pnn->mnn; }
void tn53nn(struct nns1 *pnn) { globcnn = pnn->mnl?pnn->mnl:pnn->mnn; }
void tn54nl(struct nns1 *pnn, int *pnl) { pnl = pnn->mnl?pnn->mnl:pnn->mnn; }
int tn54nn(struct nns1 *pnn, int *qnn) { qnn = pnn->mnl?pnn->mnl:pnn->mnn; return *qnn; }
int tn55nl(struct nns1 *pnn, int *qnl, int i) { return fcnn(i?(pnn->mnl?pnn->mnl:pnn->mnn):qnl); }
int tn55nn(struct nns1 *pnn, int *qnn, int i) { return fcnn(i?(pnn->mnl?pnn->mnl:pnn->mnn):qnn); }

// Probe used by accessing a struct component or pointer deref
int tn61nl(struct nns1 *pnl, struct nns1 *pnn) { return (pnl?pnl:pnn)->mrg; }
int tn62nl(struct nns2 *pnn) { return (pnn->snl?pnn->snl:pnn->snn)->mrg; }
int tn63nl(void) { return *(globnl?globnl:globnn); }
int tn64nl(void) { return *(frnl()?frnl():frnn()); }

// Probe is an array element
int *tn71nl(nna3 pnn) { return pnn[1]?pnn[1]:globnn; }
int *tn71nn(nna3 pnn) { return pnn[1]?pnn[1]:globnn; }
int tn72nl(nna3 pnn) { return fcnl(pnn[1]?pnn[1]:globnn); }
int tn72nn(nna3 pnn) { return fcnn(pnn[1]?pnn[1]:globnn); }
void tn73nl(nna3 pnn) { globcnl = pnn[1]?pnn[1]:globnn; }
void tn73nn(nna3 pnn) { globcnn = pnn[1]?pnn[1]:globnn; }
void tn74nl(nna3 pnn, int *pnl) { pnl = pnn[1]?pnn[1]:globnn; }
int tn74nn(nna3 pnn, int *qnn) { qnn = pnn[1]?pnn[1]:globnn; return *qnn; }
int tn75nl(nna3 pnn, int *qnl, int i) { return fcnn(i?(pnn[1]?pnn[1]:globnn):qnl); }
int tn75nn(nna3 pnn, int *qnn, int i) { return fcnn(i?(pnn[1]?pnn[1]:globnn):qnn); }

// Probe used by accessing an array element
int tn81nl(nna1 pnl, nna1 qnn) { return (pnl?pnl:qnn)[1]; }
int tn82nl(nna4 pnn, nna1 qnn) { return (pnn[1]?pnn[1]:qnn)[1]; }

// Probe assigned to struct component or array element
void tn91nl(struct nns1 *pnn, int *qnl, int *qnn) { pnn->mnl = qnl?qnl:qnn; }
void tn91nn(struct nns1 *pnn, int *qnl, int *qnn) { pnn->mnn = qnl?qnl:qnn; }
void tn92nl(nna3 pnl, int *qnl, int *qnn) { pnl[1] = qnl?qnl:qnn; }
void tn92nn(nna2 pnl, int *qnl, int *qnn) { pnl[1] = qnl?qnl:qnn; }

// Using MayNull values after NULL-test in statement.

// Direct use of probe in context
int sn11nl(int *pnl) { if (pnl) return fcnl(pnl); else return 0; }
int sn11nn(int *pnl) { if (pnl) return fcnn(pnl); else return 0; }
int sn12nl(void) { if (globnl) return fcnl(globnl); else return 0; }
int sn12nn(void) { if (globnl) return fcnn(globnl); else return 0; }
int sn13nl(void) { if (frnl()) return fcnl(frnl()); else return 0; }
int sn13nn(void) { if (frnl()) return fcnn(frnl()); else return 0; }
int sn14nl(int *pnl, int *qnn, int i) { if (pnl) return fcnl(i?pnl:qnn); else return 0; }
int sn14nn(int *pnl, int *qnn, int i) { if (pnl) return fcnn(i?pnl:qnn); else return 0; }

// Probe assigned to variable
void sn21nl(int *qnl) { if (qnl) globcnl = qnl; }
void sn21nn(int *qnl) { if (qnl) globcnn = qnl; }
void sn22nl(int *pnl, int *qnl) { if (qnl) pnl = qnl; }
int sn22nn(int *pnn, int *qnl) { if (qnl) pnn = qnl; return *pnn; }

// Probe returned as result
int *sn31nl(int *qnl, int *qnn) { if (qnl) return qnl; else return qnn; }
int *sn31nn(int *qnl, int *qnn) { if (qnl) return qnl; else return qnn; }

// Probe is a struct component
int *sn51nl(struct nns1 *pnn) { if (pnn->mnl) return pnn->mnl; else return pnn->mnn; }
int *sn51nn(struct nns1 *pnn) { if (pnn->mnl) return pnn->mnl; else return pnn->mnn; }
int sn52nl(struct nns1 *pnn) { if (pnn->mnl) return fcnl(pnn->mnl); else return 0; }
int sn52nn(struct nns1 *pnn) { if (pnn->mnl) return fcnn(pnn->mnl); else return 0; }
void sn53nl(struct nns1 *pnn) { if (pnn->mnl) globcnl = pnn->mnl; }
void sn53nn(struct nns1 *pnn) { if (pnn->mnl) globcnn = pnn->mnl; }
void sn54nl(struct nns1 *pnn, int *pnl) { if (pnn->mnl) pnl = pnn->mnl; }
int sn54nn(struct nns1 *pnn, int *qnn) { if (pnn->mnl) qnn = pnn->mnl; return *qnn; }
int sn55nl(struct nns1 *pnn, int *qnl, int i) { if (pnn->mnl) return fcnn(i?pnn->mnl:qnl); }
int sn55nn(struct nns1 *pnn, int *qnn, int i) { if (pnn->mnl) return fcnn(i?pnn->mnl:qnn); }

// Probe used by accessing a struct component or pointer deref
int sn61nl(struct nns1 *pnl) { if (pnl) return pnl->mrg; else return 0; }
int sn62nl(struct nns2 *pnn) { if (pnn->snl) return pnn->snl->mrg; else return 0; }
int sn63nl(void) { if (globnl) return *globnl; else return 0; }
int sn64nl(void) { if (frnl()) return *frnl(); else return 0; }

// Probe is an array element
int *sn71nl(nna3 pnn) { if (pnn[1]) return pnn[1]; else return globnn; }
int *sn71nn(nna3 pnn) { if (pnn[1]) return pnn[1]; else return globnn; }
int sn72nl(nna3 pnn) { if (pnn[1]) return fcnl(pnn[1]); else return 0; }
int sn72nn(nna3 pnn) { if (pnn[1]) return fcnn(pnn[1]); else return 0; }
void sn73nl(nna3 pnn) { if (pnn[1]) globcnl = pnn[1]; }
void sn73nn(nna3 pnn) { if (pnn[1]) globcnn = pnn[1]; }
void sn74nl(nna3 pnn, int *pnl) { if (pnn[1]) pnl = pnn[1]; }
int sn74nn(nna3 pnn, int *qnn) { if (pnn[1]) qnn = pnn[1]; return *qnn; }
int sn75nl(nna3 pnn, int *qnl, int i) { if (pnn[1]) return fcnn(i?pnn[1]:qnl); }
int sn75nn(nna3 pnn, int *qnn, int i) { if (pnn[1]) return fcnn(i?pnn[1]:qnn); }

// Probe used by accessing an array element
int sn81nl(nna1 pnl) { if (pnl) return pnl[1]; else return 0; }
int sn82nl(nna4 pnn) { if (pnn[1]) return pnn[1][1]; else return 0; }

// Probe assigned to struct component or array element
void sn91nl(struct nns1 *pnn, int *qnl) { if (qnl) pnn->mnl = qnl; }
void sn91nn(struct nns1 *pnn, int *qnl) { if (qnl) pnn->mnn = qnl; }
void sn92nl(nna3 pnl, int *qnl) { if (qnl) pnl[1] = qnl; }
void sn92nn(nna2 pnl, int *qnl) { if (qnl) pnl[1] = qnl; }

// Using MayNull values in correct context after complex test including NULL-test(s)

// One NULL-test with other tests
int cn11(int *pnl, int i) { return (i>5 && pnl)?fcnn(pnl):fcnl(pnl); }
int cn12(int *pnl, int i) { return (i>5 && i<20 && pnl)?fcnn(pnl):fcnl(pnl); }
int cn13(int *pnl, int i) { return (i>5 && pnl && i<20)?fcnn(pnl):fcnl(pnl); }
int cn14(int *pnl, int i) { return (i>5 && pnl && *pnl<20)?fcnn(pnl):fcnl(pnl); }
int cn15(int *pnl, int i) { return (pnl && i>5 && *pnl<20)?fcnn(pnl):fcnl(pnl); }
int cn16(int *pnl, int i) { return (i>5 || pnl)?fcnl(pnl):fcnl(pnl); }
int cn17(int *pnl, int i) { return (pnl == NULL || i > 5)?fcnl(pnl):fcnn(pnl); }
int cn18(int *pnl, int i) { return (i > 5 || NULL == pnl || *pnl<20)?fcnl(pnl):fcnn(pnl); }
int cn19(int *pnl, int i) { return (i > 5 || !pnl)?fcnl(pnl):fcnn(pnl); }

// Two NULL-tests and possibly other tests
int cn21(int *pnl, int *qnl, int i) { return (pnl && qnl)?fcnn(pnl)+fcnn(qnl):fcnl(pnl)+fcnl(qnl); }
int cn22(int *pnl, int *qnl, int i) { return (i > 5 && pnl && qnl)?fcnn(pnl)+fcnn(qnl):fcnl(pnl)+fcnl(qnl); }
int cn23(int *pnl, int *qnl, int i) { return (pnl && i > 5 && qnl)?fcnn(pnl)+fcnn(qnl):fcnl(pnl)+fcnl(qnl); }
int cn24(int *pnl, int *qnl, int i) { return (pnl && qnl && i > 5)?fcnn(pnl)+fcnn(qnl):fcnl(pnl)+fcnl(qnl); }
int cn25(int *pnl, int *qnl, int i) { return (pnl || qnl)?fcnl(pnl)+fcnl(qnl):fcnl(pnl)+fcnl(qnl); }
int cn26(int *pnl, int *qnl, int i) { return (pnl == NULL || qnl == NULL)?fcnl(pnl)+fcnl(qnl):fcnn(pnl)+fcnn(qnl); }
int cn27(int *pnl, int *qnl, int i) { return (pnl == NULL || (*pnl == 1 && qnl && *qnl == 1))?fcnl(pnl)+fcnl(qnl):fcnn(pnl)+fcnl(qnl); }

// One NULL-test with other tests in statement
int cn31(int *pnl, int i) { if (i>5 && pnl) return fcnn(pnl); else return fcnl(pnl); }
int cn32(int *pnl, int i) { if (i>5 && i<20 && pnl) return fcnn(pnl); return fcnl(pnl); }
int cn33(int *pnl, int i) { if (i>5 && pnl && i<20) return fcnn(pnl); else return fcnl(pnl); }
int cn34(int *pnl, int i) { if (i>5 && pnl && *pnl<20) return fcnn(pnl); else return fcnl(pnl); }
int cn35(int *pnl, int i) { if (pnl && i>5 && *pnl<20) return fcnn(pnl); else return fcnl(pnl); }
int cn36(int *pnl, int i) { if (i>5 || pnl) return fcnl(pnl); else return fcnl(pnl); }
int cn37(int *pnl, int i) { if (pnl == NULL || i > 5) return fcnl(pnl); else return fcnn(pnl); }
int cn38(int *pnl, int i) { if (i > 5 || NULL == pnl || *pnl<20) return fcnl(pnl); else return fcnn(pnl); }
int cn39(int *pnl, int i) { if (i > 5 || !pnl) return fcnl(pnl); else return fcnn(pnl); }

// Two NULL-tests and possibly other tests in statement
int cn41(int *pnl, int *qnl, int i) { if (pnl && qnl) return fcnn(pnl)+fcnn(qnl); else return fcnl(pnl)+fcnl(qnl); }
int cn42(int *pnl, int *qnl, int i) { if (i > 5 && pnl && qnl) return fcnn(pnl)+fcnn(qnl); else return fcnl(pnl)+fcnl(qnl); }
int cn43(int *pnl, int *qnl, int i) { if (pnl && i > 5 && qnl) return fcnn(pnl)+fcnn(qnl); else return fcnl(pnl)+fcnl(qnl); }
int cn44(int *pnl, int *qnl, int i) { if (pnl && qnl && i > 5) return fcnn(pnl)+fcnn(qnl); else return fcnl(pnl)+fcnl(qnl); }
int cn45(int *pnl, int *qnl, int i) { if (pnl || qnl) return fcnl(pnl)+fcnl(qnl); else return fcnl(pnl)+fcnl(qnl); }
int cn46(int *pnl, int *qnl, int i) { if (pnl == NULL || qnl == NULL) return fcnl(pnl)+fcnl(qnl); else return fcnn(pnl)+fcnn(qnl); }
int cn47(int *pnl, int *qnl, int i) { if (pnl == NULL || (*pnl == 1 && qnl && *qnl == 1)) return fcnl(pnl)+fcnl(qnl); else return fcnn(pnl)+fcnl(qnl); }

// Modify tested probe between uses in correct context

int mn11(int *pnl) { return pnl?(*pnl + (pnl = NULL, fcnl(pnl))):fcnl(pnl); }
int mn12(int *pnl, int i) { if (pnl) { i = *pnl; i += fcnn(pnl); pnl = NULL; return i + fcnl(pnl); } else return fcnl(pnl); }

