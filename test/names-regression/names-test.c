#include <stddef.h>

#define NAM1_CONST 1
#define NAM2_CONST 2
#define NAM3_CONST 3

typedef int names_t;
typedef int nam2_t;
typedef int nam3_t;

struct names_str { int m; };
struct nam2_str { int M; };
struct nam3_str { int m; };

enum names_enum { NAM1_EL1, NAM1EL2 };
enum nam2_enum { NAM2_EL1, NAM2EL2 };
enum nam3_enum { NAM3_EL1, NAM3EL2 };

ptrdiff_t names_var;
size_t nam2_var;
int nam3_var;

void names_fun(int);
void nam2_fun(int);
void nam3_fun(void);

int names_fun2(int i, int J) { names_fun(5); return i+J; }
int nam2_fun2(int i) { nam2_fun(5); return i+NAM1_CONST; }
int nam3_fun2(int i) { nam3_fun(); return i+NAM2_CONST; }

size_t (*names_funp)(names_t names_p, nam2_t nam2_p, nam3_t nam3_p);
