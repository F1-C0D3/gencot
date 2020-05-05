// read-only type examples:
typedef int *intP_t;
typedef const int *intCP_t;
typedef const struct point { int x,y,z; } *coord3dCP_t;
typedef int funBinPtr_t(const int *p1, int p2);
typedef const int *funResPtr_t(int p1, int p2);
typedef const struct sphere { struct point *center; int radius; } *sphereP_t;
typedef const struct sphereC { coord3dCP_t center; int radius; } *sphereCP_t;
typedef int intA_t[3];
typedef const int intCA_t[3];
typedef const sphereP_t spherePA_t[3];
typedef const sphereCP_t sphereCPA_t[3];
typedef void funArrPar_t(intA_t,intCA_t,spherePA_t,sphereCPA_t);
typedef struct arrstr { intA_t m1; intCA_t m2; spherePA_t m3; sphereCPA_t m4; } arrstr_t;

// String type examples:
typedef char *charP_t;
typedef const char *charCP_t;

// Additional result examples for function types:
typedef short funLinPar1_t(int*,char);
typedef void funLinPar2_t(int*,char);
typedef short funLinPar3_t(int*,char*);
typedef short funLinPar4_t(const int*,char*);

// Additional result examples for function pointer types:
typedef short (*funLinPar1P_t)(int*,char);
typedef void (*funLinPar2P_t)(int*,char);
typedef short (*funLinPar3P_t)(int*,char*);
typedef short (*funLinPar4P_t)(const int*,char*);

struct s { int arr[3]; };
