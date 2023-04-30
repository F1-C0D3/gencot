// Using values of readonly type.

// Functions used as context:
void fcln(int *i) {}
void fcro(int *i) {}
// Global variables used as context:
int *globcln;
int *globcro;

// global readonly probes:
int *glob; // global const-val variable
int *frro(void); // (external) function with readonly result

// source of linear value:
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
void f11ln(int *pro) { fcln(pro); }
void f11ro(int *pro) { fcro(pro); }
void f12ln(void) { fcln(glob); }
void f12ro(void) { fcro(glob); }
void f13ln(void) { fcln(frro()); }
void f13ro(void) { fcro(frro()); }
void f14ln(int *pro, int *qro, int i) { fcln(i?pro:qro); }
void f14ro(int *pro, int *qro, int i) { fcro(i?pro:qro); }

// Probe assigned to variable
void f21ln(void) { globcln = frro(); }
void f21ro(void) { globcro = frro(); }
void f22ln(int *pln) { pln = frro(); }
void f22ro(int *pro) { pro = frro(); }

// Probe returned as result
int *f31ln(void) { return frro(); }
int *f31ro(void) { return frro(); }

// Probe used in conditional expression with other branch as context
void f41ln(int *pro, int *qln, int i) { fcro(i?pro:qln); }
void f42ln(int *pln, int *qro, int i) { fcro(i?pln:qro); }

// Probe used by accessing a struct component
void f51ln(struct ros1 *pro) { pro->mrg = 5; }
void f51ro(struct ros1 *pro) { pro->mrg; }
void f52ln(struct ros1 *pro) { pro->mro = frro(); }
void f52ro(struct ros1 *pro) { pro->mro; }
void f53ln(struct ros1 *pro) { pro->mln = frln(); }
void f53ro(struct ros1 *pro) { pro->mln; }
void f54ln(struct ros1 *pro) { *(pro->mln) = 5; }
void f54ro(struct ros1 *pro) { *(pro->mln); }
void f55ln(struct ros1 *pro) { fcln(pro->mln); }
void f55ro(struct ros1 *pro) { fcro(pro->mln); }
void f56ln(struct ros1 *pro) { globcln = pro->mln; }
void f56ro(struct ros1 *pro) { globcro = pro->mln; }
void f57ln(struct ros1 *pro, int *pln) { pln = pro->mln; }
void f57ro(struct ros1 *pro, int *qro) { qro = pro->mln; }
int *f58ln(struct ros1 *pro) { return pro->mln; }
int *f58ro(struct ros1 *pro) { return pro->mln; }
void f59ln(struct ros1 *pro, int *qln, int i) { fcro(i?pro->mln:qln); }
void f59ro(struct ros1 *pro, int *qro, int i) { fcro(i?pro->mln:qro); }

void f61ln(struct ros2 *pro) { pro->sln->mrg = 5; }
void f61ro(struct ros2 *pro) { pro->sln->mrg; }
void f62ln(struct ros2 *pro) { pro->sln->mro = frro(); }
void f62ro(struct ros2 *pro) { pro->sln->mro; }
void f63ln(struct ros2 *pro) { pro->sln->mln = frln(); }
void f63ro(struct ros2 *pro) { pro->sln->mln; }

// Probe used by accessing an array element
void f71ln(roa1 pro) { pro[1] = 5; }
void f71ro(roa1 pro) { pro[1]; }
void f72ln(roa2 pro) { pro[1] = frro(); }
void f72ro(roa2 pro) { pro[1]; }
void f73ln(roa3 pro) { pro[1] = frln(); }
void f73ro(roa3 pro) { pro[1]; }
void f74ln(roa3 pro) { *(pro[1]) = 5; }
void f74ro(roa3 pro) { *(pro[1]); }
void f75ln(roa3 pro) { fcln(pro[1]); }
void f75ro(roa3 pro) { fcro(pro[1]); }
void f76ln(roa3 pro) { globcln = pro[1]; }
void f76ro(roa3 pro) { globcro = pro[1]; }
void f77ln(roa3 pro, int *qln) { qln = pro[1]; }
void f77ro(roa3 pro, int *qro) { qro = pro[1]; }
int *f78ln(roa3 pro) { return pro[1]; }
int *f78ro(roa3 pro) { return pro[1]; }
void f79ln(roa3 pro, int *qln, int i) { fcro(i?pro[1]:qln); }
void f79ro(roa3 pro, int *qro, int i) { fcro(i?pro[1]:qro); }

void f81ln(roa4 pro) { pro[1][1] = 5; }
void f81ro(roa4 pro) { pro[1][1]; }
void f82ln(roa5 pro) { pro[1][1] = frro(); }
void f82ro(roa5 pro) { pro[1][1]; }
void f83ln(roa6 pro) { pro[1][1] = frln(); }
void f83ro(roa6 pro) { pro[1][1]; }

// probe assigned to struct component or array element
void f91ln(struct ros1 *pln) { pln->mln = frro(); }
void f91ro(struct ros1 *pln) { pln->mro = frro(); }
void f92ln(roa3 pln) { pln[1] = frro(); }
void f92ro(roa2 pln) { pln[1] = frro(); }

