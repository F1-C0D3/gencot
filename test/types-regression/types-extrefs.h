struct extstrt1 { int m1,m2; };  // used transitively by extstrt2
struct extstrt2 { int m1,m2; struct extstrt1 s; };  // used transitively by extstr2
struct extstr1 { int m1,m2; };  // referenced by function declaration
struct extstr2 { int m1,m2; struct extstrt2 s; };  // referenced by typedef
struct extstr3 { int m1,m2; };  // referenced by function definition
struct extstr4 { int m1,m2; };  // referenced by member declaration
struct extstr5 { int m1,m2; };  // listed
struct extstr6 { int m1,m2; };  // referenced by unused external function
struct extstr7 { int m1,m2; };  // not used

typedef int exttyp1;  // referenced by function declaration
typedef int exttyp2;  // referenced by typedef
typedef int exttyp3;  // referenced by function definition
typedef int exttyp4;  // referenced by member declaration
typedef int exttyp5;  // listed
typedef int exttyp6;  // referenced by unused external function
typedef int exttyp7;  // not used

typedef int *exttypt0;   // used transitively by exttypt1
typedef struct { exttypt0 m; } exttypt1;  // used transitively by exttypt2, anonymous
typedef int (*exttypt2)(exttypt1);  // used transitively by exttypt3
typedef exttypt2 exttypt3;  // used transitively by exttypt4
typedef struct extstrt { exttypt3 m; } exttypt4; // used transitively by exttypt5, named
typedef exttypt4 *exttypt5; //  used transitively by exttypt6
typedef exttypt5 exttypt6[2]; //  listed

typedef const char *exttypc1;  // chain end
typedef exttypc1 exttypc2;
typedef exttypc2 exttypc3;  // referenced by function definition
typedef exttypc3 exttypc4;
typedef exttypc4 exttypc5;

typedef int extfunt1(int,int);
