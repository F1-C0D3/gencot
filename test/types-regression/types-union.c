union x { int m; } dummy; // to prevent collision with tagless structs when combining symbol tables
union { int m11, m12; } var_union;
union uni { int m21, m22; } var_tunion;
union { int m31; int m32:4; int m33:2; } var_bfunion1;
union { int m41; int m42:20; int m43:5; int m44:20; int m45:12; } var_bfunion2;
union uni var_tunion2;
union { short m51; union { char m52; long long m53; } m54; } var_nunion;
