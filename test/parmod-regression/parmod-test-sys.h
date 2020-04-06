typedef int extfunt1(int,int); // referenced by internal declaration
typedef int extfunt2(int,int); // referenced by external declarations of invoked functions
typedef int extfunt3(int,char*); // referenced by external typedefs

extern extfunt2 extfun1a;  // invoked, externally declared using function typedef
extern extfunt2 extfun1b;  // invoked, externally declared using function typedef

typedef struct extstrt { extfunt3 *m1, *m2; } exttypt1; // used by internal declaration
 
