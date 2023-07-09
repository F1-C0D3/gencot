// Using values of readonly type.

// Functions used as context:
int fcln(int *i) { return 0; }
int fcro(int *i) { return 0; }
// Global variables used as context:
int *globcln;
int *globcro;

// global readonly probes:
int *glob; // global const-val variable
int *frro(void); // (external) function with readonly result

// global linear probes:
int *globln; // global const-val variable
int *frln(void); // (external) function with linear result

// struct probes:
struct ros1 { int mrg; int *mro; int *mln; };
struct ros2 { struct ros1 *sln; struct ros1 sub; };

// array probes:
typedef int roa1[5];  // regular elements
typedef int* roa2[5]; // readonly elements
typedef int* roa3[5]; // linear elements
typedef roa1 roa4[5];   // array elements
typedef roa2 roa5[5];   // array elements
typedef roa3 roa6[5];   // array elements

// Direct use of probe in context
int f11ln(int *pro) { return fcln(pro); }
int f11ro(int *pro) { return fcro(pro); }
int f12ln(void) { return fcln(glob); }
int f12ro(void) { return fcro(glob); }
int f13ln(void) { return fcln(frro()); }
int f13ro(void) { return fcro(frro()); }
int f14ln(int *pro, int *qro, int i) { return fcln(i?pro:qro); }
int f14ro(int *pro, int *qro, int i) { return fcro(i?pro:qro); }

// Probe assigned to variable
void f21ln(void) { globcln = frro(); }
void f21ro(void) { globcro = frro(); }
void f22ln(int *pln) { pln = frro(); }
int f22ro(int *pro) { pro = frro(); return *pro; }

// Probe returned as result
int *f31ln(void) { return frro(); }
int *f31ro(void) { return frro(); }

// Probe used in conditional expression with other branch as context
int f41ln(int *pro, int *qln, int i) { return fcro(i?pro:qln); }
int f42ln(int *pln, int *qro, int i) { return fcro(i?pln:qro); }

// Probe used by accessing a struct component
struct ros1 *f51ln(struct ros1 *pro) { pro->mrg = 5; return pro; }
int f51ro(struct ros1 *pro) { return pro->mrg; }
struct ros1 *f52ln(struct ros1 *pro) { pro->mro = frro(); return pro; }
int *f52ro(struct ros1 *pro) { return pro->mro; }
struct ros1 *f53ln(struct ros1 *pro) { pro->mln = frln(); return pro; }
int *f53ro(struct ros1 *pro) { return pro->mln; }
struct ros1 *f54ln(struct ros1 *pro) { *(pro->mln) = 5; return pro; }
int f54ro(struct ros1 *pro) { return *(pro->mln); }
int f55ln(struct ros1 *pro) { return fcln(pro->mln); }
int f55ro(struct ros1 *pro) { return fcro(pro->mln); }
void f56ln(struct ros1 *pro) { globcln = pro->mln; }
void f56ro(struct ros1 *pro) { globcro = pro->mln; }
void f57ln(struct ros1 *pro, int *pln) { pln = pro->mln; }
int f57ro(struct ros1 *pro, int *qro) { qro = pro->mln; return *qro; }
int *f58ln(struct ros1 *pro) { return pro->mln; }
int *f58ro(struct ros1 *pro) { return pro->mln; }
int f59ln(struct ros1 *pro, int *qln, int i) { return fcro(i?pro->mln:qln); }
int f59ro(struct ros1 *pro, int *qro, int i) { return fcro(i?pro->mln:qro); }

struct ros2 *f61ln(struct ros2 *pro) { pro->sln->mrg = 5; return pro; }
int f61ro(struct ros2 *pro) { return pro->sln->mrg; }
struct ros2 *f62ln(struct ros2 *pro) { pro->sln->mro = frro(); return pro; }
int *f62ro(struct ros2 *pro) { return pro->sln->mro; }
struct ros2 *f63ln(struct ros2 *pro) { pro->sln->mln = frln(); return pro; }
int *f63ro(struct ros2 *pro) { return pro->sln->mln; }
struct ros2 *f64ln(struct ros2 *pro) { pro->sub.mln = frln(); return pro; }
int *f64ro(struct ros2 *pro) { return pro->sub.mln; }

// Probe used by accessing an array element
int f71ln(roa1 pro) { pro[1] = 5; return pro[1]; }
int f71ro(roa1 pro) { return pro[1]; }
int *f72ln(roa2 pro) { pro[1] = frro(); return pro[1]; }
int *f72ro(roa2 pro) { return pro[1]; }
int *f73ln(roa3 pro) { pro[1] = frln(); return pro[1]; }
int *f73ro(roa3 pro) { return pro[1]; }
int *f74ln(roa3 pro) { *(pro[1]) = 5; return pro[1]; }
int f74ro(roa3 pro) { return *(pro[1]); }
int f75ln(roa3 pro) { return fcln(pro[1]); }
int f75ro(roa3 pro) { return fcro(pro[1]); }
void f76ln(roa3 pro) { globcln = pro[1]; }
void f76ro(roa3 pro) { globcro = pro[1]; }
void f77ln(roa3 pro, int *qln) { qln = pro[1]; }
int f77ro(roa3 pro, int *qro) { qro = pro[1]; return *qro; }
int *f78ln(roa3 pro) { return pro[1]; }
int *f78ro(roa3 pro) { return pro[1]; }
int f79ln(roa3 pro, int *qln, int i) { return fcro(i?pro[1]:qln); }
int f79ro(roa3 pro, int *qro, int i) { return fcro(i?pro[1]:qro); }

int f81ln(roa4 pro) { pro[1][1] = 5; return pro[1][1]; }
int f81ro(roa4 pro) { return pro[1][1]; }
int *f82ln(roa5 pro) { pro[1][1] = frro(); return pro[1][1]; }
int *f82ro(roa5 pro) { return pro[1][1]; }
int *f83ln(roa6 pro) { pro[1][1] = frln(); return pro[1][1]; }
int *f83ro(roa6 pro) { return pro[1][1]; }

// probe assigned to struct component or array element
void f91ln(struct ros1 *pln) { pln->mln = frro(); }
void f91ro(struct ros1 *pln) { pln->mro = frro(); }
void f92ln(roa3 pln) { pln[1] = frro(); }
void f92ro(roa2 pln) { pln[1] = frro(); }

// Using values of linear type (can be banged).

// Direct use of probe in context
int g11ln(int *pln) { return fcln(pln); }
int g11ro(int *pln) { return fcro(pln); }
int g12ln(void) { return fcln(globln); }
int g12ro(void) { return fcro(globln); }
int g13ln(void) { return fcln(frln()); }
int g13ro(void) { return fcro(frln()); }
int g14ln(int *pln, int *qln, int i) { return fcln(i?pln:qln); }
int g14ro(int *pln, int *qln, int i) { return fcro(i?pln:qln); }

// Probe assigned to variable
void g21ln(void) { globcln = frln(); }
void g21ro(void) { globcro = frln(); }
void g22ln(int *pln) { pln = frln(); }
int g22ro(int *pro) { pro = frln(); return *pro; }

// Probe returned as result
int *g31ln(void) { return frln(); }
int *g31ro(void) { return frln(); }

// Probe used by accessing a struct component
void g51ln(struct ros1 *pln) { pln->mrg = 5; }
int g51ro(struct ros1 *pln) { return pln->mrg; }
void g52ln(struct ros1 *pln) { pln->mro = frln(); }
int *g52ro(struct ros1 *pln) { return pln->mro; }
void g53ln(struct ros1 *pln) { pln->mln = frln(); }
int *g53ro(struct ros1 *pln) { return pln->mln; }
int g54ln(struct ros1 *pln) { *(pln->mln) = 5; }
int g54ro(struct ros1 *pln) { *(pln->mln); }
int g55ln(struct ros1 *pln) { return fcln(pln->mln); }
int g55ro(struct ros1 *pln) { return fcro(pln->mln); }
void g56ln(struct ros1 *pln) { globcln = pln->mln; }
void g56ro(struct ros1 *pln) { globcro = pln->mln; }
void g57ln(struct ros1 *pln, int *qln) { qln = pln->mln; }
int g57ro(struct ros1 *pln, int *qro) { qro = pln->mln; return *qro; }
int *g58ln(struct ros1 *pln) { return pln->mln; }
int *g58ro(struct ros1 *pln) { return pln->mln; }
int g59ln(struct ros1 *pln, int *qln, int i) { return fcro(i?pln->mln:qln); }
int g59ro(struct ros1 *pln, int *qro, int i) { return fcro(i?pln->mln:qro); }

void g61ln(struct ros2 *pln) { pln->sln->mrg = 5; }
int g61ro(struct ros2 *pln) { return pln->sln->mrg; }
void g62ln(struct ros2 *pln) { pln->sln->mro = frln(); }
int *g62ro(struct ros2 *pln) { return pln->sln->mro; }
void g63ln(struct ros2 *pln) { pln->sln->mln = frln(); }
int *g63ro(struct ros2 *pln) { return pln->sln->mln; }
void g64ln(struct ros2 *pln) { pln->sub.mro = frln(); }
int *g64ro(struct ros2 *pln) { return pln->sub.mro; }

// Probe used by accessing an array element
void g71ln(roa1 pln) { pln[1] = 5; }
int g71ro(roa1 pln) { return pln[1]; }
void g72ln(roa2 pln) { pln[1] = frln(); }
int *g72ro(roa2 pln) { return pln[1]; }
void g73ln(roa3 pln) { pln[1] = frln(); }
int *g73ro(roa3 pln) { return pln[1]; }
void g74ln(roa3 pln) { *(pln[1]) = 5; }
int g74ro(roa3 pln) { return *(pln[1]); }
int g75ln(roa3 pln) { return fcln(pln[1]); }
int g75ro(roa3 pln) { return fcro(pln[1]); }
void g76ln(roa3 pln) { globcln = pln[1]; }
void g76ro(roa3 pln) { globcro = pln[1]; }
void g77ln(roa3 pln, int *qln) { qln = pln[1]; }
int g77ro(roa3 pln, int *qro) { qro = pln[1]; return *qro; }
int *g78ln(roa3 pln) { return pln[1]; }
int *g78ro(roa3 pln) { return pln[1]; }
int g79ln(roa3 pln, int *qln, int i) { return fcro(i?pln[1]:qln); }
int g79ro(roa3 pln, int *qro, int i) { return fcro(i?pln[1]:qro); }

void g81ln(roa4 pln) { pln[1][1] = 5; }
int g81ro(roa4 pln) { return pln[1][1]; }
void g82ln(roa5 pln) { pln[1][1] = frln(); }
int *g82ro(roa5 pln) { return pln[1][1]; }
void g83ln(roa6 pln) { pln[1][1] = frln(); }
int *g83ro(roa6 pln) { return pln[1][1]; }

// probe assigned to struct component or array element
void g91ln(struct ros1 *pln) { pln->mln = frln(); }
void g91ro(struct ros1 *pln) { pln->mro = frln(); }
void g92ln(roa3 pln) { pln[1] = frln(); }
void g92ro(roa2 pln) { pln[1] = frln(); }

// banging in nested bang positions
struct ros1 *n11(struct ros1 *pln, int i) { i = pln->mrg; *(pln->mln) = i; return pln; }
struct ros1 *n12(struct ros1 *pln, int i) { i = pln->mrg; i += *(pln-> mro); *(pln->mln) = i; return pln; }

// banging in binding sequences
struct ros1 *bs11(struct ros1 *pln, int i) { return i = pln->mrg, *(pln->mln) = i, pln; }
struct ros1 *bs12(struct ros1 *pln, int *qro, int i) { return qro = pln->mln, i = *qro, pln->mrg = i, pln; }
struct ros1 *bs13(struct ros1 *pln, int *qro, int *i) { return qro = pln->mln, *i = *qro, pln->mln = i, pln; }
