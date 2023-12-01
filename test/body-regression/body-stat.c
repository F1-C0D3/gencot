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

int ss1(int i) {
    switch (i) {
        case 0: return i;
    }
}

int ss2(int i) {
    switch (i) {
        default: return 0;
    }
}

int ss3(int i) {
    switch (i) {
        case 0: return i;
        default: return 0;
    }
}

int ss4(int i) {
    switch (i) {
        case 0: return i;
        case 1: return i+5;
        default: return 0;
    }
}

int ss5(int i) {
    switch (i) {
        case 0: return i;
        default: return 0;
        case 1: return i+5;
    }
}

int ss6(int i, int j) {
    switch (i) {
        case 0: j = i;
        case 1: i++;
        case 2: j = 5;
        default: return j;
    }
}

int ss7(int i, int j) {
    switch (i) {
        i++;
        case 0: j = i;
        case 1: i++; break;
        case 2: j = 5;
    }
    return j;
}

int ss8(int i, int j) {
    switch (i) {
        case 0: j = i;
        case 1: switch (j) {
          case 0: return 17;
          default: return i;
        }
        case 2: j = 5;
    }
    return j;
}

int ss10(int i) {
    switch (i) return i;
}

int ss11(int i) {
    switch (i) if (i==0) break;
    return i;
}

int ss12(int i) {
    switch (i) i = 5;
    return i;
}

int ss13(int i,int j) {
    switch (i) {
        case 0: j = i;
        if (i < 5) { j++; case 3: j++; }
        else { case 1: return i+5;
               case 7: j--; }
        default: return 0;
    }
}

int ss14(int i) {
    switch (i) {
        int j = 0;
        case 0: j = i;
        case 1: i++; break;
        case 2: j = 5;
    }
    return i;
}

int ss15(int i, int j) {
    switch (i) {
        case 0: j = i; int k = 0; 
        case 1: i++; break;
        case 2: j = k;
    }
    return j;
}
