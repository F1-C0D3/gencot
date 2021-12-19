int lf1(int a, int b) {
    for (int i=0;i<b;i++) a*=2;
    return a;
}
int lf2(int i) {
    for (;i<5;i++);
    return i;
}
int lf3(int i) {
    for (;i<5;i++) continue;
    return i;
}
int lf4(int i) {
    for (;i<5;i++) break;
    return i;
}
int lf5(int i) {
    for (;i<5;i++) return i;
    return i;
}
int lf6(int i) {
    for (;i<=5;i++);
    return i;
}
int lf7(int i) {
    for (i=12;i>5;i--);
    return i;
}
int lf8(int i) {
    for (i=12;i>=5;i--);
    return i;
}
int lf9(int i) {
    for (;i<5;i+=3);
    return i;
}
int lf10(int i) {
    for (;i<5;i=i+3);
    return i;
}
int lf11(int i) {
    for (;i<5;i=3+i);
    return i;
}
int lf12(int i) {
    for (i=12;i>=5;i-=3);
    return i;
}
int lf13(int i) {
    for (i=12;i>=5;i=i-3);
    return i;
}
int lf14(int i, int j) {
    for (;i<j;i++);
    return i;
}
int lf15(int i) {
    for (i=0;i!=5;i++);
    return i;
}
int lf16(int i) {
    for (i=10;i!=5;i--);
    return i;
}

int lfe1(int i) {
    for (;i<5;i++) i=0;
    return i;
}
int lfe2(int i, int j) {
    for (;i<j;i++) j=0;
    return i;
}
int lfe3(int i) {
    for (;i<i+5;i++);
    return i;
}
int lfe4(int i,int j) {
    for (;i<j;i++,j++);
    return i;
}
int lfe5(int i) {
    for (;i<5;i--);
    return i;
}
int lfe6(int i) {
    for (;i>5;i--);
    return i;
}
int lfe7(int i) {
    for (;i!=5;i++);
    return i;
}
int lfe8(int i) {
    for (i=3;i!=5;i--);
    return i;
}
int lfe9(int i) {
    for (i=10;i!=5;i++);
    return i;
}
int lfe10(int i) {
    for (i=0;i!=5;i+=2);
    return i;
}
