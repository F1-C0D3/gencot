// Integral type examples:
typedef int int_t;
typedef unsigned int uint_t;
typedef short short_t;
typedef char char_t;
typedef long long_t;

// Floating point type examples:
typedef float float_t;
typedef double double_t;

// Enumeration type examples:
typedef enum { RED, GREEN, BLUE } color_t;
typedef enum shape { CIRC=10, SQUARE=20 } shape_t;

// Structure type examples:
typedef struct { int x; int y; } coord2d_t;
typedef struct point { int x,y,z; } coord3d_t;
typedef struct line { coord2d_t p1,p2; } line2d_t;
typedef struct colshp { shape_t shp; color_t col; } colshp_t;

// Union type examples: 
typedef union { coord2d_t p2d; coord3d_t p3d; } coord_t;
typedef union pointorline { coord_t pt; line2d_t ln; } pol_t;

// Function type examples:
typedef int funUnary_t(int);
typedef color_t funBinary_t(int p1, int p2);
typedef void funVoidRes_t(shape_t param);
typedef char funVoidPar_t(void);
//typedef struct point funIncomplete_t();
typedef coord3d_t funVariadic_t(int,long,...);

// Pointer type examples:
typedef struct point *coord3dP_t;
typedef struct sphere { coord3dP_t center; int radius; } *sphereP_t;
typedef int *intP_t;
typedef enum shape *shapeP_t;
typedef int **intPP_t;

// Function pointer type examples:
typedef int (*funUnaryP_t)(int);
typedef color_t (*funBinaryP_t)(int p1, int p2);
typedef void (*funVoidResP_t)(shape_t param);
typedef char (*funVoidParP_t)(void);
//typedef struct point funIncomplete_t();
typedef coord3d_t (*funVariadicP_t)(int,long,...);
typedef int funHigher_t(int fpar(int), char);
typedef int (*funHigherP_t)(int fpar(int), char);

// Array type examples:
typedef int intA_t[5];
typedef struct line line2dA_t[10];
typedef int *intPA_t[10];
typedef int (*intAP_t)[7];
typedef struct { intA_t a1; intPA_t a2; intAP_t a3; } arrays_t;
typedef int funArray_t(intA_t p1, intAP_t p2);
typedef int intAA_t[3][5];
