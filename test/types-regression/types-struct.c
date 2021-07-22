struct { int m11, m12; } var_struct;
struct str { int m21, m22; } var_tstruct;
struct { int m31; int m32:4; int m33:2; } var_bfstruct1;
struct { int m41; int m42:20; int m43:5; int m44:20; int m45:12; } var_bfstruct2;
struct str var_tstruct2;
struct { short m51; 
    struct { char m52; long long m53; } m54; 
} var_nstruct;

// A derived function type with an anonymous struct type as result type. 
// Here the source file name is needed by gencot-dvdtypes!
typedef struct { int m6; } (*f_anonstrfunt)(void);
