void sv1(void) {}
void sv2(int i) {}
void sv3(void) {;}
void sv4(void) { return;}

int se1(int i) { return i; }
int se2(int i) { return (i + 5)* i; }
int se3(int i) { i++; return i; }
int se4(int i) { i++; i = 5; return i; }
int se5(int i) { i++; return ++i; }

int si1(int i, int j) {
    if (i == 0) return j; 
    else return i; }
int si2(int i, int j) {
    if (i == 0) return j; 
    return i; }
int si3(int i, int j) {
    if (i == 0) i = 10; 
    else i += j; 
    return i; }
int si4(int i, int j) {
    if (i == 0) i = 10; 
    else if (j == 0) j = i; 
         else i += j; 
    return i+j; }
int si5(int i, int j) {
    if (i == 0) {
        if (j == 0) i = 10;
        else j += 10;}
    else if (j == 0) j = i; 
         else i += j; 
    return i+j; }
int si6(int i, int j) {
    if (i == 0) {
        if (j == 0) i = 10;
        else return j += 10;}
    else if (j == 0) return j = i; 
         else i += j; 
    return i+j; }
int si8(int i, int j) {
    if (i == 0) j++;
    else i++;
    j = 2*j;
    return 2*i; }
int si9(int i, int j) {
    if (i == 0) j++;
    else i++;
    i = 2*j;
    return 2*j; }

int sc1(int i, int j) {
    i += 2*j;
    j += 2*i;
    i = i+j;
    return j*i;}
int sc2(int i, int j) {
    i += 2*j;
    if (i > 13) {
        j += 2*i;
        i += 2*j;
    } else {
        i++;
        j--;
    }
    if (j == 0) j = 15;
    i += j;
    return i;}

int sd1(int i, int j) {
    i += 2*j;
    int k = j+7;
    j += i+k;
    k += j+i;
    return k;}
int sd2(int i, int j) {
    i += 2*j;
    { int i = j+7;
      j += i+i;
      i += j+i;}
    return i;}
int sd3(int i, int j) {
    i += 2*j;
    { int k = j+7;
      j += i+k;
      k = 15;}
    i += j+i;
    return i;}
int sd4(int i, int j) {
    i += 2*j;
    if (i == 0) { 
        int k = j+7;
        j += i+k;
        k = 15;}
    else j = i+3;
    i += j+i;
    return i;}
int sd5(int i, int j) {
    i += 2*j;
    int k1,k2;
    k1 = i+1;
    k2 = j+1;
    j += k1+k2;
    k1 += j+i;
    return k1;}
int sd6(int i, int j) {
    i += 2*j;
    int k1,k2 = 42;
    k1 = i+1;
    j += k1+k2;
    k1 += j+i;
    return k1;}
