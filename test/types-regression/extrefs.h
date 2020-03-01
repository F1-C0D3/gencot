typedef int exttypt1;  // used transitively by exttypt2
typedef int (*exttypt2)(exttypt1);  // used transitively by exttypt3
typedef exttypt2 exttypt3;  // used transitively by exttypt4
typedef struct unit { exttypt3 m; } exttypt4; // used transitively by exttypt5
typedef exttypt4 *exttypt5; //  used transitively by exttypt6
typedef exttypt5 exttypt6[2]; //  listed

