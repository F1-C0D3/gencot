theory Gencot_CArray_Lemmas
  imports "Gencot_CArray_Tuples"
begin

section "Support for Reasoning with C Arrays"

text \<open>
We introduce an overloaded abstract data type for all C arrays with 
indexes of type nat. It consists of two selector functions and two constructor
functions which reflect the main ways how to work with arrays in C.
The second constructor comes in two variants for either fixed size arrays 
or variable sized arrays.
\<close>
consts 
  siz :: "'arr \<Rightarrow> nat"
  elm :: "nat \<Rightarrow> 'arr \<Rightarrow> 'el"
  elm_update :: "nat \<Rightarrow> ('el \<Rightarrow> 'el) \<Rightarrow> 'arr \<Rightarrow> 'arr"
  elms_fill :: "(nat \<Rightarrow> 'el) \<Rightarrow> 'arr"
  elms_fill_n :: "nat \<Rightarrow> (nat \<Rightarrow> 'el) \<Rightarrow> 'arr"

text \<open>
Additionally we define derived functions as abbreviations for typical use cases.
\<close>
consts
  vld :: "'arr \<Rightarrow> nat \<Rightarrow> bool"
  elm_modified :: "nat \<Rightarrow> ('el \<Rightarrow> 'el \<Rightarrow> bool) \<Rightarrow> 'arr \<Rightarrow> 'arr \<Rightarrow> bool"

subsection "Fixed Sized Arrays"

text \<open>
For every actual wrapper record (i.e., array size) the following locale 
will be interpreted. It extends CArrFuns by the laws of the abstract data type, 
and semantics theorems for the Gencot array operations.\<close>

locale CArrLems = CArrFuns fld wrp
  for 
    fld :: "'arr \<Rightarrow> ('n::len, 'el) FixedList" and 
    wrp :: "('n, 'el) FixedList \<Rightarrow> 'arr" +
  assumes 
    fld_inverse: "\<And>x. wrp (fld x) = x" and 
    wrp_inverse: "\<And>x. fld (wrp x) = x"
begin

text \<open>Define conversion functions between lists and the wrapper record.\<close>
definition lstFxd :: "'arr \<Rightarrow> 'el list"
  where lstFxd_def[simp]: "lstFxd a \<equiv> Rep_FixedList (fld a)"
definition arrFxd :: "'el list \<Rightarrow> 'arr"
  where arrFxd_def[simp]: "arrFxd a \<equiv> wrp (Abs_FixedList a)"

text \<open>Define the abstract data type functions for the wrapper record.\<close>
definition sizFxd :: "'arr \<Rightarrow> nat"
  where "sizFxd a \<equiv> length (lstFxd a)"
definition elmFxd :: "nat \<Rightarrow> 'arr \<Rightarrow> 'el"
  where "elmFxd i a \<equiv> nth (lstFxd a) i"
definition elm_updateFxd :: "nat \<Rightarrow> ('el \<Rightarrow> 'el) \<Rightarrow> 'arr \<Rightarrow> 'arr"
  (* Define elm_updateFxd as total, so that elm_distUpd needs no assumption *)
  where "elm_updateFxd i f a \<equiv> 
    if i < LENGTH('n) then arrFxd (list_update (lstFxd a) i (f (elmFxd i a))) else a"
definition elms_fillFxd :: "(nat \<Rightarrow> 'el) \<Rightarrow> 'arr"
  where "elms_fillFxd f \<equiv> arrFxd [f x . x \<leftarrow> [0 ..< LENGTH('n)]]"

lemmas unfold = sizFxd_def elmFxd_def elm_updateFxd_def elms_fillFxd_def

text \<open>Additional derived functions\<close>
definition vldFxd :: "'arr \<Rightarrow> nat \<Rightarrow> bool"
  where vldFxd_def[simp]: "vldFxd a i \<equiv> i < sizFxd a"
definition elm_modifiedFxd :: "nat \<Rightarrow> ('el \<Rightarrow> 'el \<Rightarrow> bool) \<Rightarrow> 'arr \<Rightarrow> 'arr \<Rightarrow> bool"
  where elm_modified_def: "elm_modifiedFxd i m a1 a2 \<equiv> 
    m (elmFxd i a1) (elmFxd i a2) \<and> (\<forall>j \<noteq> i. vldFxd a1 j \<longrightarrow> elmFxd j a1 = elmFxd j a2)"

text \<open>Arrays are never empty.\<close>
lemma arrNotNil: "\<forall>x::'arr .  lstFxd x \<noteq> []"
  apply(rule allI)
  apply(unfold lstFxd_def)
  apply(cut_tac x = "(fld x)" in Rep_FixedList )
  by auto

text \<open>Simplification rules for selectors siz and elm\<close>
lemma sizArr[simp]: "sizFxd a = LENGTH('n)"
  apply(unfold sizFxd_def lstFxd_def)
  by (simp add: length_FixedList)
lemma elmElmUpd[simp]: "vldFxd a i \<Longrightarrow> elmFxd i (elm_updateFxd i f a) = f (elmFxd i a)"
  apply(simp add: unfold wrp_inverse)
  apply(cut_tac x = "(fld a)" in Rep_FixedList )
  by(simp add: Abs_FixedList_inverse)
lemma elmElmsFill[simp]: "i < LENGTH('n) \<Longrightarrow> elmFxd i (elms_fillFxd f) = f i"
  by(simp add: unfold wrp_inverse Abs_FixedList_inverse)
lemma elmElmUpdFrame[simp]: "vldFxd a i \<and> vldFxd a j \<and> i \<noteq> j \<Longrightarrow> elmFxd j (elm_updateFxd i f a) = elmFxd j a"
  apply(auto simp add: elm_updateFxd_def elmFxd_def)
  apply(cut_tac x = "(fld a)" in Rep_FixedList )
  apply(subst wrp_inverse)
  apply(subst Abs_FixedList_inverse)
  by (auto)

text \<open>Reasoning rules for elm_update\<close>
lemma elm_identUpd[simp]: "elm_updateFxd i (\<lambda>a. a) = (\<lambda>a. a)"
  by(auto simp add: unfold Rep_FixedList_inverse fld_inverse)
lemma elm_sameUpd: "elm_updateFxd i (\<lambda>_. m (elmFxd i x)) x = elm_updateFxd i m x"
  by(simp add: unfold)
lemma elm_distUpd: "(elm_updateFxd i f) \<circ> (elm_updateFxd i g) = elm_updateFxd i (f \<circ> g)"
  for f:: "'el \<Rightarrow> 'el"
  apply(rule ext,simp add: unfold)
  apply(cut_tac x = "(fld x)" in Rep_FixedList )
  by(simp add: wrp_inverse  Abs_FixedList_inverse)

lemma elm_commUpd_elm: "i < j \<Longrightarrow> (elm_updateFxd j m2) \<circ> (elm_updateFxd i m1) = (elm_updateFxd i m1) \<circ> (elm_updateFxd j m2)"
  apply(rule ext,simp add: unfold)
  apply(cut_tac x = "(fld x)" in Rep_FixedList )
  by(simp add: wrp_inverse Abs_FixedList_inverse list_update_swap)

text \<open>Array equality by extensionality. \<close>
lemma eqArr1: "(\<And> i. (vldFxd a1 i) \<Longrightarrow> ((elmFxd i a1) = (elmFxd i a2))) \<Longrightarrow> (a1 = a2)"
  apply(unfold elmFxd_def vldFxd_def sizFxd_def lstFxd_def)
  apply(drule nth_equalityI[rotated],simp add: length_FixedList)
  apply(drule Rep_FixedList_inject[THEN iffD1])
  apply(drule arg_cong[where f = wrp])
  by(simp add: fld_inverse)

lemma eqArr: "(a1 = a2) = 
              (\<forall> i. (vldFxd a1 i) \<longrightarrow> ((elmFxd i a1) = (elmFxd i a2)))"
  apply(rule iffI,simp)
  by (rule eqArr1,auto)

lemma eqElmUpd: "vldFxd a2 i \<Longrightarrow> (a1 = elm_updateFxd i f a2) =
                 ((elmFxd i a1) = f (elmFxd i a2) \<and> (\<forall> j. j \<noteq> i \<and> (vldFxd a1 j) \<longrightarrow> (elmFxd j a1) = (elmFxd j a2)))"
  apply(rule iffI,simp)
  apply(simp add: eqArr)
   apply(rule allI)
  apply(case_tac "ia = i")
  by(auto)

lemma eqElmsFill: "(a = elms_fillFxd f) = 
                 ((\<forall> i. (vldFxd a i) \<longrightarrow> ((elmFxd i a) = f i)))"
  apply(rule iffI,simp)
  by(simp add: eqArr)

text \<open>Semantics theorems for the Gencot array operations.\<close>

definition ctrct_getArrFxd :: "'arr \<times> ('m::len) word \<Rightarrow> bool"
  where ctrct_getArrFxd_def[simp]:
  "ctrct_getArrFxd x \<equiv> let (a,i) = x in vldFxd a (unat i)"
theorem sem_getArr: 
 "ctrct_getArrFxd (a,i) \<Longrightarrow> 
  getArrFxd (a,i) = elmFxd (unat i) a"
  by (simp add: getArrFxd_def getArr'_def elmFxd_def)
theorem errsem_getArr:
 "\<not> ctrct_getArrFxd (a,i) \<Longrightarrow> 
  getArrFxd (a,i) = elmFxd 0 a"
  apply(simp add: getArrFxd_def getArr'_def elmFxd_def)
  apply(fold lstFxd_def)
  apply(case_tac " lstFxd a")
   apply(cut_tac arrNotNil)
  by auto

definition ctrct_setArrFxd :: "'arr \<times> ('m::len) word \<times> 'el \<Rightarrow> bool"
  where ctrct_setArrFxd_def[simp]:
  "ctrct_setArrFxd x \<equiv> let (a,i,v) = x in vldFxd a (unat i)"
theorem sem_setArr: 
 "ctrct_setArrFxd (a,i,v) \<Longrightarrow> 
  setArrFxd (a,i,v) = (elm_updateFxd (unat i) (\<lambda>_.v) a, ())"
  by (simp add: setArrFxd_def setArr'_def elm_updateFxd_def)
theorem errsem_setArr:
 "\<not> ctrct_setArrFxd (a,i,v) \<Longrightarrow> 
  setArrFxd (a,i,v) = (a,())"
  by (simp add: setArrFxd_def setArr'_def fld_inverse)

definition ctrct_modifyArrFxd :: "'arr \<times> ('m::len) word \<times> ('el \<times> 'arg \<Rightarrow> 'el \<times> 'out) \<times> 'arg \<Rightarrow> bool"
  where ctrct_modifyArrFxd_def[simp]:
  "ctrct_modifyArrFxd x \<equiv> let (a,(i,f,v)) = x in vldFxd a (unat i)"
theorem sem_modifyArr:
 "ctrct_modifyArrFxd (a,x) \<Longrightarrow> 
  modifyArrFxd (a,x) = 
  (let (i,f,x) = x; (e,y) = f (elmFxd (unat i) a, x) in (elm_updateFxd (unat i) (\<lambda>_.e) a, y))"
  by (simp add: modifyArrFxd_def modifyArr'_def split_def Let_def elm_updateFxd_def elmFxd_def)
theorem errsem_modifyArr:
 "\<not> ctrct_modifyArrFxd (a,x) ==> 
  modifyArrFxd (a,x) = (let (i,f,x) = x in modifyArrFxd (a,(0,f,x)))"
  by (simp add: modifyArrFxd_def modifyArr'_def split_def Let_def fld_inverse)

definition ctrct_modrefArrFxd :: "'arr \<times> ('m::len) word \<times> ('pel \<times> 'arg \<Rightarrow> 'pel \<times> 'out) \<times> 'arg \<Rightarrow> bool"
  where ctrct_modrefArrFxd_def[simp]:
  "ctrct_modrefArrFxd x \<equiv> let (a,(i,f,v)) = x in vldFxd a (unat i)"
theorem sem_modrefArr:
 "ctrct_modrefArrFxd (a,x) \<Longrightarrow> 
  modrefArrFxd (a,x) = 
  (let (i,f,x) = x; (e,y) = f (toPtr (elmFxd (unat i) a), x) in (elm_updateFxd (unat i) (\<lambda>_.frPtr e) a, y))"
  by (simp add: modrefArrFxd_def modrefArr'_def split_def Let_def elm_updateFxd_def elmFxd_def)
theorem errsem_modrefArr:
 "\<not> ctrct_modrefArrFxd (a,x) ==> 
  modrefArrFxd (a,x) = (let (i,f,x) = x in modrefArrFxd (a,(0,f,x)))"
  by (simp add: modrefArrFxd_def modrefArr'_def split_def Let_def fld_inverse)

end

subsection "Array Pointers and Pairs"

text \<open>
This corresponds to a direct application of the abstract data type to arbitrary lists.
Additionally, an update function for pairs is defined. Together they are the basis
for explicitly sized arrays.
\<close>

text \<open>Define the abstract data type functions for lists.\<close>

definition sizPtr :: "'el CArrPtr\<^sub>T \<Rightarrow> nat"
  where "sizPtr a \<equiv> length a"
definition elmPtr :: "nat \<Rightarrow> 'el CArrPtr\<^sub>T \<Rightarrow> 'el"
  where "elmPtr i a \<equiv> nth a i"
definition elm_updatePtr :: "nat \<Rightarrow> ('el \<Rightarrow> 'el) \<Rightarrow> 'el CArrPtr\<^sub>T \<Rightarrow> 'el CArrPtr\<^sub>T"
  (* Define elm_updatePtr as total, so that elm_distUpdPtr needs no assumption *)
  where "elm_updatePtr i f a \<equiv> if i < length a then list_update a i (f (nth a i)) else a"
definition elms_fill_nPtr :: "nat \<Rightarrow> (nat \<Rightarrow> 'el) \<Rightarrow> 'el CArrPtr\<^sub>T"
  where "elms_fill_nPtr n f \<equiv> [f x . x \<leftarrow> [0 ..< n]]"

text \<open>Define the function for updating the first component of a pair.\<close>

definition fst_update :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<times> 'b) \<Rightarrow> ('a \<times> 'b)"
  where "fst_update f x = (f (fst x),snd x)"

lemmas unfoldPtr = sizPtr_def elmPtr_def elm_updatePtr_def elms_fill_nPtr_def fst_update_def

text \<open>Additional derived functions\<close>
definition vldPtr :: "'el CArrPtr\<^sub>T \<Rightarrow> nat \<Rightarrow> bool"
  where vldPtr_def[simp]: "vldPtr a i \<equiv> i < sizPtr a"
definition elm_modifiedPtr :: "nat \<Rightarrow> ('el \<Rightarrow> 'el \<Rightarrow> bool) \<Rightarrow> 'el CArrPtr\<^sub>T \<Rightarrow> 'el CArrPtr\<^sub>T \<Rightarrow> bool"
  where "elm_modifiedPtr i m a1 a2 \<equiv> 
    m (elmPtr i a1) (elmPtr i a2) \<and> (\<forall>j \<noteq> i. vldPtr a1 j \<longrightarrow> elmPtr j a1 = elmPtr j a2)"
lemmas elm_modified_defPtr = elm_modifiedPtr_def

adhoc_overloading siz sizPtr
  and vld vldPtr
  and elm elmPtr
  and elm_update elm_updatePtr
  and elm_modified elm_modifiedPtr
  and elms_fill_n elms_fill_nPtr

definition fst_modified :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'b) \<Rightarrow> ('a \<times> 'b) \<Rightarrow> bool"
  where "fst_modified m x1 x2 \<equiv> 
    m (fst x1) (fst x2) \<and> (snd x1) = (snd x2)"

text \<open>Simplification rules for selectors siz, elm, and fst\<close>
lemma sizElmUpdPtr[simp]: "sizPtr (elm_updatePtr i f a) = sizPtr a"
  by(simp add: unfoldPtr)
lemma sizElmsFillPtr[simp]: "sizPtr (elms_fill_nPtr n f) = n"
  by(simp add: unfoldPtr)
lemma elmElmUpdPtr[simp]: "vldPtr a i \<Longrightarrow> elmPtr i (elm_updatePtr i f a) = f (elmPtr i a)"
  by(simp add: unfoldPtr)
lemma elmElmUpdFramePtr[simp]: "vldPtr a i \<and> vldPtr a j \<and> i \<noteq> j \<Longrightarrow> elmPtr j (elm_updatePtr i f a) = elmPtr j a"
  by(simp add: unfoldPtr)
lemma elmElmsFillPtr[simp]: "i < n \<Longrightarrow> elmPtr i (elms_fill_nPtr n f) = f i"
  by(simp add: unfoldPtr)
lemma fstFstUpd[simp]: "fst (fst_update f a) = f (fst a)"
  by(auto simp add: fst_update_def)
lemma fstFstUpdFrame[simp]: "snd (fst_update f a) = snd a"
  by(auto simp add: fst_update_def)

text \<open>Reasoning rules for elm_update and fst_update\<close>
lemma elm_identUpdPtr[simp]: "elm_updatePtr i (\<lambda>a. a) = (\<lambda>a. a)"
  by (rule ext,simp add: unfoldPtr)
lemma elm_sameUpdPtr: "elm_updatePtr i (\<lambda>_. m (elmPtr i x)) x = elm_updatePtr i m x"
  by(simp add: unfoldPtr)
lemma elm_distUpdPtr: "(elm_updatePtr i f) \<circ> (elm_updatePtr i g) = elm_updatePtr i (f \<circ> g)"
  by (rule ext,simp add: unfoldPtr)
lemma elm_commUpd_elmPtr: "i < j \<Longrightarrow> (elm_updatePtr j m2) \<circ> (elm_updatePtr i m1) = (elm_updatePtr i m1) \<circ> (elm_updatePtr j m2)"
  apply (unfold elm_updatePtr_def elmPtr_def)
  apply(rule ext,simp,rule impI)
  apply(rule list_update_swap)
  by(simp)
lemma fst_identUpd[simp]: "fst_update (\<lambda>a. a) = (\<lambda>a. a)"
  apply (unfold fst_update_def)
  by(simp)
lemma fst_sameUpd: "fst_update (\<lambda>_. m (fst x)) x = fst_update m x"
  by(simp add: fst_update_def)
lemma fst_distUpd: "(fst_update f) \<circ> (fst_update g) = fst_update (f \<circ> g)"
  apply (unfold fst_update_def)
  by(auto)

text \<open>Array equality by extensionality. \<close>
lemma eqArrPtr: "sizPtr a1 = sizPtr a2 \<Longrightarrow>
              (a1 = a2) = 
              (\<forall> i. (vldPtr a1 i) \<longrightarrow> ((elmPtr i a1) = (elmPtr i a2)))"
  for a1::"'el CArrPtr\<^sub>T" and a2::"'el CArrPtr\<^sub>T"
  apply(rule iffI) apply(rule allI,rule impI)
   apply(auto simp add: unfoldPtr)
  apply(case_tac a1)
  apply(case_tac a2)
  apply(auto)
  apply(rule nth_equalityI)
  by(auto)

lemma eqElmUpdPtr: "sizPtr a1 = sizPtr a2 \<Longrightarrow> vldPtr a2 i \<Longrightarrow> (a1 = elm_updatePtr i f a2) =
                 ((elmPtr i a1) = f (elmPtr i a2) \<and> (\<forall> j. j \<noteq> i \<and> (vldPtr a1 j) \<longrightarrow> (elmPtr j a1) = (elmPtr j a2)))"
  apply(rule iffI,simp)
  apply(simp add: eqArrPtr)
  apply(rule allI)
  apply(case_tac "ia = i")
   by(auto)

lemma eqElmsFillPtr: "sizPtr a = n \<Longrightarrow> (a = elms_fill_nPtr n f) = 
                 ((\<forall> i. (vldPtr a i) \<longrightarrow> ((elmPtr i a) = f i)))"
  apply(rule iffI,simp)
  by(simp add: eqArrPtr)

subsection "Explicitly Sized Arrays"

text \<open>
The abstract data type is applied to pairs consisting of a list and an explicit size.
The explicit size is ignored and the intrinsic size of the list is used.
\<close>

text \<open>Define the abstract data type functions and a wellformedness predicate for pairs.\<close>

definition sizES :: "'el CArrES\<^sub>T \<Rightarrow> nat"
  where "sizES a \<equiv> sizPtr (fst a)"
definition elmES :: "nat \<Rightarrow> 'el CArrES\<^sub>T \<Rightarrow> 'el"
  where "elmES i a \<equiv> elmPtr i (fst a)"
definition elm_updateES :: "nat \<Rightarrow> ('el \<Rightarrow> 'el) \<Rightarrow> 'el CArrES\<^sub>T \<Rightarrow> 'el CArrES\<^sub>T"
  where "elm_updateES i f a \<equiv> fst_update (elm_updatePtr i f) a"
definition elms_fill_nES :: "nat \<Rightarrow> (nat \<Rightarrow> 'el) \<Rightarrow> 'el CArrES\<^sub>T"
  where "elms_fill_nES n f \<equiv> (elms_fill_nPtr n f,of_nat n)"
definition wlfES :: "'el CArrES\<^sub>T \<Rightarrow> bool"
  where "wlfES a \<equiv> sizPtr (fst a) = (unat (snd a)) \<and> sizPtr (fst a) > 0"

lemmas unfoldES = sizES_def elmES_def elm_updateES_def elms_fill_nES_def wlfES_def

text \<open>Additional derived functions\<close>
definition vldES :: "'el CArrES\<^sub>T \<Rightarrow> nat \<Rightarrow> bool"
  where vldES_def[simp]: "vldES a i \<equiv> i < sizES a"
definition elm_modifiedES :: "nat \<Rightarrow> ('el \<Rightarrow> 'el \<Rightarrow> bool) \<Rightarrow> 'el CArrES\<^sub>T \<Rightarrow> 'el CArrES\<^sub>T \<Rightarrow> bool"
  where "elm_modifiedES i m a1 a2 \<equiv> 
    m (elmES i a1) (elmES i a2) \<and> (\<forall>j \<noteq> i. vldES a1 j \<longrightarrow> elmES j a1 = elmES j a2)"
lemmas elm_modified_defES = elm_modifiedES_def

adhoc_overloading siz sizES
  and vld vldES
  and elm elmES
  and elm_update elm_updateES
  and elm_modified elm_modifiedES
  and elms_fill_n elms_fill_nES

text \<open>Wellformedness implies nonempty and size limit\<close>

lemma wlfsizES: "wlfES a \<Longrightarrow> sizES a > 0 \<and> sizES a < 2^64"
  apply(cut_tac unat_lt2p[of "(snd a)"])
  by(simp add: unfoldES)

text \<open>Simplification rules for selectors siz and elm and the wellformedness predicate.\<close>

lemma sizElmUpdES[simp]: "sizES (elm_updateES i f a) = sizES a"
  by(simp add: unfoldES)
lemma sizElmsFillES[simp]: "sizES (elms_fill_nES n f) = n"
  by(simp add: unfoldES)
lemma elmElmUpdES[simp]: "vldES a i \<Longrightarrow> elmES i (elm_updateES i f a) = f (elmES i a)"
  by(simp add:unfoldES)
lemma elmElmUpdFrameES[simp]: "vldES a i \<and> vldES a j \<and> i \<noteq> j \<Longrightarrow> elmES j (elm_updateES i f a) = elmES j a"
  by(simp add:unfoldES)
lemma elmElmsFillES[simp]: "i < n \<Longrightarrow> elmES i (elms_fill_nES n f) = f i"
  by(simp add:unfoldES)
lemma wlfElmUpdES[simp]: "wlfES (elm_updateES i f a) = wlfES a"
  by(simp add: unfoldES)
lemma wlfElmsFillES[simp]: "n > 0 \<and> n < 2^64 \<Longrightarrow> wlfES (elms_fill_nES n f)"
  by(simp add: unfoldES unat_of_nat)

text \<open>Reasoning rules for elm_update\<close>

lemma elm_identUpdES[simp]: "elm_updateES i (\<lambda>a. a) = (\<lambda>a. a)"
  by (rule ext,simp add: unfoldES)
lemma elm_sameUpdES: "elm_updateES i (\<lambda>_. m (elmES i x)) x = elm_updateES i m x"
  apply(simp add: unfoldES)
  apply(subst fst_sameUpd[symmetric])
  apply(subst elm_sameUpdPtr)
  apply(subst fst_sameUpd)
  by(simp)
lemma elm_distUpdES: "(elm_updateES i f) \<circ> (elm_updateES i g) = elm_updateES i (f \<circ> g)"
  for f:: "'el \<Rightarrow> 'el" and a::"'el CArrES\<^sub>T"
  apply (rule ext,simp add: unfoldES)
  apply(subst comp_apply[symmetric,where f="fst_update f" and g="fst_update g" for f g])
  apply(subst fst_distUpd)
  apply(subst elm_distUpdPtr)
  by(simp)
lemma elm_commUpd_elmES: "i < j \<Longrightarrow> (elm_updateES j m2) \<circ> (elm_updateES i m1) = (elm_updateES i m1) \<circ> (elm_updateES j m2)"
  apply (unfold elm_updateES_def elmES_def)
  apply(subst fst_distUpd)+
  apply(subst elm_commUpd_elmPtr)
  by(auto)

text \<open>Array equality by extensionality. \<close>
lemma eqArrES: "wlfES a1 \<and> wlfES a2 \<and> sizES a1 = sizES a2 \<Longrightarrow>
              (a1 = a2) = 
              (\<forall> i. (vldES a1 i) \<longrightarrow> ((elmES i a1) = (elmES i a2)))"
  for a1::"'el CArrES\<^sub>T" and a2::"'el CArrES\<^sub>T"
  apply(rule iffI,rule allI,rule impI)
   apply(auto simp add: unfoldES)
  apply(case_tac a1)
  apply(case_tac a2)
  by(auto simp add: eqArrPtr)

lemma eqElmUpdES: 
 "wlfES a1 \<and> wlfES a2 \<and> sizES a1 = sizES a2 \<and> vldES a2 i \<Longrightarrow> 
  (a1 = elm_updateES i f a2) =
  ((elmES i a1) = f (elmES i a2) \<and> (\<forall> j. j \<noteq> i \<and> (vldES a1 j) \<longrightarrow> (elmES j a1) = (elmES j a2)))"
  apply(rule iffI,simp)
  apply(simp add: eqArrES)
  apply(rule allI)
  apply(case_tac "ia = i")
  by(auto)

lemma eqElmsFillES: "wlfES a \<and> sizES a = n \<Longrightarrow> (a = elms_fill_nES n f) =
                 ((\<forall> i. (vldES a i) \<longrightarrow> ((elmES i a) = f i)))"
  apply(erule conjE)+
  apply(frule wlfsizES)
  apply(rule iffI,simp)
  by(simp add: eqArrES)

text \<open>Semantics theorems for the Gencot array operations.\<close>

definition ctrct_getArrES :: "'el CArrES\<^sub>T \<times> ('m::len) word \<Rightarrow> bool"
  where ctrct_getArrES_def[simp]:
    "ctrct_getArrES x \<equiv> let (a,i) = x in vldES a (unat i)"
theorem sem_getArrES[sem]: 
 "wlfES a \<and> ctrct_getArrES (a,i) \<Longrightarrow> 
  getArrES (a,i) = elmES (unat i) a"
  by (simp add: getArrES_def Let_def split_def unfoldES unfoldPtr)
theorem errsem_getArrES:
 "wlfES a \<and> \<not> ctrct_getArrES (a,i) \<Longrightarrow> 
  getArrES (a,i) = elmES 0 a"
  apply(erule conjE)+
  apply(frule wlfsizES)
  apply (simp add: getArrES_def Let_def split_def unfoldES unfoldPtr)
  apply(rule hd_conv_nth)
  by (simp)

definition ctrct_setArrES :: "'el CArrES\<^sub>T \<times> ('m::len) word \<times> 'el \<Rightarrow> bool"
  where ctrct_setArrES_def[simp]:
  "ctrct_setArrES x \<equiv> let (a,i,v) = x in vldES a (unat i)"
theorem sem_setArrES[sem]: 
 "wlfES a \<and> ctrct_setArrES (a,i,v) \<Longrightarrow> 
  setArrES (a,i,v) = ((elm_updateES (unat i) (\<lambda>_.v) a), ())"
  by (simp add: setArrES_def Let_def split_def unfoldES unfoldPtr)
theorem errsem_setArrES:
 "wlfES a \<and> \<not> ctrct_setArrES (a,i,v) \<Longrightarrow> 
  setArrES (a,i,v) = (a,())"
  by (simp add: setArrES_def Let_def split_def unfoldES unfoldPtr)

definition ctrct_modifyArrES :: "'el CArrES\<^sub>T \<times> ('m::len) word \<times> ('el \<times> 'arg \<Rightarrow> 'el \<times> 'out) \<times> 'arg \<Rightarrow> bool"
  where ctrct_modifyArrES_def[simp]:
  "ctrct_modifyArrES x \<equiv> let (a,(i,f,v)) = x in vldES a (unat i)"
theorem sem_modifyArrES[sem]:
 "wlfES a \<and> ctrct_modifyArrES (a,x) \<Longrightarrow> 
  modifyArrES (a,x) = 
  (let (i,f,x) = x; (e,y) = f (elmES (unat i) a, x) 
  in ((elm_updateES (unat i) (\<lambda>_.e) a), y))"
  by (simp add: modifyArrES_def Let_def split_def unfoldES unfoldPtr)
theorem errsem_modifyArrES:
 "wlfES a \<and> \<not> ctrct_modifyArrES (a,x) ==> 
  modifyArrES (a,x) = (let (i,f,x) = x in modifyArrES (a,(0,f,x)))"
  by (simp add: modifyArrES_def split_def unfoldES unfoldPtr)

definition ctrct_modrefArrES :: "'el CArrES\<^sub>T \<times> ('m::len) word \<times> ('pel \<times> 'arg \<Rightarrow> 'pel \<times> 'out) \<times> 'arg \<Rightarrow> bool"
  where ctrct_modrefArrES_def[simp]:
  "ctrct_modrefArrES x \<equiv> let (a,(i,f,v)) = x in vldES a (unat i)"
theorem sem_modrefArrES[sem]:
 "wlfES a \<and> ctrct_modrefArrES (a,x) \<Longrightarrow> 
  modrefArrES (a,x) = 
  (let (i,f,x) = x; (e,y) = f (toPtr (elmES (unat i) a), x) 
  in ((elm_updateES (unat i) (\<lambda>_.frPtr e) a), y))"
  by (simp add: modrefArrES_def Let_def split_def unfoldES unfoldPtr)
theorem errsem_modrefArrES:
 "wlfES a \<and> \<not> ctrct_modrefArrES (a,x) ==> 
  modrefArrES (a,x) = (let (i,f,x) = x in modrefArrES (a,(0,f,x)))"
  by (simp add: modrefArrES_def split_def unfoldES unfoldPtr)

subsection "Array Conversion Functions"

context CArrLems
begin

text \<open>Semantics theorems.\<close>

theorem sem_toCAES:
 "toCAESFxd a = elms_fill_nES (sizFxd a) (\<lambda>i. elmFxd i a)"
  apply(simp add: toCAESFxd_def toCAES'_def unfoldES unfoldPtr unfold)
  apply(subst map_nth[symmetric])
  by(simp add: length_FixedList)

theorem sem_fromCAES:
 "sizES a = LENGTH('n) \<Longrightarrow> 
  fromCAESFxd a = elms_fillFxd (\<lambda>i. elmES i a)"
  apply(simp add: fromCAESFxd_def fromCAES'_def unfoldES unfoldPtr unfold) 
  apply(subst map_nth[symmetric])
  by(auto)

theorem sem_rotoCAES[simp]: "rotoCAESFxd = toCAESFxd"
  apply(rule ext)
  by(simp add: rotoCAESFxd_def toCAESFxd_def)

theorem sem_rofromCAES[simp]: "rofromCAESFxd = fromCAESFxd"
  apply(rule ext)
  by(simp add: rofromCAESFxd_def fromCAESFxd_def)

text \<open>
The following rules can be used for simplifying reasoning when the semantics
is applied by omitting the semantics of the conversion functions.
\<close>

text \<open>Simplification rules for selectors siz and elm and the wellformedness predicate.\<close>

lemma sizToCAES[simp]: 
 "sizES (toCAESFxd a) = sizFxd a"
  by(simp add: sem_toCAES)
lemma elmToCAES[simp]:
 "vldFxd a i \<Longrightarrow> elmES i (toCAESFxd a) = elmFxd i a"
  by(simp add: sem_toCAES)
lemma wlfToCAES[simp]:
 "sizFxd a < 2^64 \<Longrightarrow> wlfES (toCAESFxd a)"
  by(simp add: sem_toCAES)
lemma sizFromCAES[simp]: 
 "sizES a = LENGTH('n) \<Longrightarrow> 
  sizFxd (fromCAESFxd a) = sizES a"
  by(simp)
lemma elmFromCAES[simp]:
 "sizES a = LENGTH('n) \<and> vldES a i \<Longrightarrow> 
  elmFxd i (fromCAESFxd a) = elmES i a"
  by(simp add: sem_fromCAES)

text \<open>Inversion rules for the conversion functions.\<close>
lemma toCAES_inverse: 
 "fromCAESFxd (toCAESFxd a) = a"
  apply(rule sym)
  by(simp add: sem_toCAES sem_fromCAES eqElmsFill)

lemma fromCAES_inverse: 
 "wlfES a \<and> sizES a = LENGTH('n) \<Longrightarrow>
  toCAESFxd (fromCAESFxd a) = a"
  apply(rule sym)
  by(simp add: sem_toCAES sem_fromCAES eqElmsFillES)

text \<open>Rules for applying the conversion functions.\<close>

lemma fromCAESElmUpd:
 "vld a i \<and> sizES a = LENGTH('n) \<Longrightarrow>
  fromCAESFxd (elm_updateES i m a) = elm_updateFxd i m (fromCAESFxd a)"
  by(simp add: sem_fromCAES eqElmUpd)
lemma fromCAESElmsFill:
 "n = LENGTH('n) \<Longrightarrow>
  fromCAESFxd (elms_fill_nES n f) = elms_fillFxd f"
  by(simp add: sem_fromCAES eqElmsFill)
lemmas fromCAES_apply = fromCAESElmUpd fromCAESElmsFill

lemma toCAESElmUpd:
 "sizFxd a < 2^64 \<and> vldFxd a i \<Longrightarrow>
  toCAESFxd (elm_updateFxd i m a) = elm_updateES i m (toCAESFxd a)"
  by(simp add: sem_toCAES eqElmUpdES)
lemma toCAESElmsFill:
 "n < 2^64 \<and>n = LENGTH('n) \<Longrightarrow>
  toCAESFxd (elms_fillFxd f) = elms_fill_n n f"
  by(simp add: sem_toCAES eqElmsFillES)
lemmas toCAES_apply = toCAESElmUpd toCAESElmsFill

end

end
