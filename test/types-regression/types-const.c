const int var_cint; // nonlinear
const int *var_pcint; // readonly
int * const var_cpint; // not readonly
const int * const var_cpcint; // readonly

typedef const int ciname; // nonlinear
typedef const int *pciname; // readonly
typedef int * const cpiname; // not readonly
typedef const int * const pcpiname; // readonly
typedef int (*pfname)(int); // nonlinear
ciname var_ciname; // nonlinear
pciname var_pciname; // readonly
cpiname var_cpiname; // not readonly
pcpiname var_pcpiname; // readonly

const struct cspint { int m11; int * m12; } var_cspint, *var_pcspint; // nonlinear, not readonly
const struct cspcint { int m21; const int * m22; } var_cspcint, *var_pcspcint; // nonlinear, readonly
const struct cspintpcint { int m31; const int * m32; int * m33; } var_cspintpcint, *var_pcspintpcint; // nonlinear, not readonly
const struct cspfun { int m41; int (*m42)(int); } var_cspfun, *var_pcspfun;  // nonlinear, readonly
const struct cscpiname { int m11; cpiname m12; } var_cscpiname, *var_pcscpiname; // nonlinear, not readonly
const struct cspciname { int m21; pciname m22; } var_cspciname, *var_pcspciname; // nonlinear, readonly
const struct cspinamepciname { int m31; pciname m32; cpiname m33; } var_cspinamepciname, *var_pcspinamepciname; // nonlinear, not readonly
const struct cspfname { int m41; pfname m42; } var_cspfname, *var_pcspfname; // nonlinear, readonly

void fc_int(const int p_cint, const int *p_pcint,int * const p_cpint, const int * const p_pcpint) {} // nonlinear, readonly, not readonly, readonly
void fc_iname(ciname p_cint, pciname p_pcint,cpiname p_cpint, pcpiname p_pcpint) {} // nonlinear, readonly, not readonly, readonly
void fcs_int(const struct cspint * p1, const struct cspcint *p2, const struct cspintpcint *p3, const struct cspfun *p4) {} // not readonly, readonly, not readonly, readonly
void fcs_iname(const struct cscpiname * p1, const struct cspciname *p2, const struct cspinamepciname *p3, const struct cspfname *p4) {} // not readonly, readonly, not readonly, readonly

struct cstr {
const int m_cint; // nonlinear
const int *m_pcint; // readonly
int * const m_cpint; // not readonly
const int * const m_cpcint; // readonly
ciname m_ciname; // nonlinear
pciname m_pciname; // readonly
cpiname m_cpiname; // not readonly
pcpiname m_pcpiname; // readonly
};

const int var_acint[5]; // readonly
const int *var_apcint[5]; // array of pointers to const int; not readonly: array elements can be assigned
int * const var_acpint[5]; // array of constant pointers to int; not readonly: pointer targets can be assigned
const int * const var_acpcint[5]; // readonly: neither array elements nor pointer targets can be assigned
ciname var_aciname[5]; // readonly
pciname var_apciname[5]; // not readonly
cpiname var_acpiname[5]; // not readonly
pcpiname var_apcpiname[5]; // readonly
const struct cspint var_acspint[5]; // not readonly: *m12 in cspint can be assigned
const struct cspint *var_apcspint[5]; // not readonly: array elements can be assigned
const struct cspint * const var_acpcspint[5]; // not readonly: *m12 in cspint can be assigned
const struct cspcint var_acspcint[5]; // readonly
const struct cspcint *var_apcspcint[5]; // not readonly: array elements can be assigned
const struct cspcint * const var_acpcspcint[5]; // readonly
const struct cspintpcint var_acspintpcint[5], *var_apcspintpcint[5]; // not readonly, not readonly
const struct cspfun var_acspfun[5]; // readonly
const struct cspfun *var_apcspfun[5]; // not readonly: array elements can be assigned
const struct cspfun * const var_acpcspfun[5]; // readonly
const struct cscpiname var_acscpiname[5], *var_apcscpiname[5]; // not readonly, not readonly
const struct cspciname var_acspciname[5]; // readonly
const struct cspciname *var_apcspciname[5]; // not readonly: array elements can be assigned
const struct cspciname * const var_acpcspciname[5]; // readonly
const struct cspinamepciname var_acspinamepciname[5], *var_apcspinamepciname[5]; // not readonly, not readonly
const struct cspfname var_acspfname[5]; // readonly
const struct cspfname *var_apcspfname[5]; // not readonly: array elements can be assigned
const struct cspfname * const var_acpcspfname[5]; // readonly


