theory Gencot_ESArray_Lemmas
  imports "Gencot_ESArray_Tuples"
    "Gencot_CArray_Lemmas"
begin

text \<open>Extend the overloaded abstract data type to explicitly sized arrays.
      Additionally introduce the following function for filling an array 
      with an explicitly specified size.\<close>
consts 
  arr_fill_n :: "nat \<Rightarrow> (nat \<Rightarrow> 'el) \<Rightarrow> 'arr"

text \<open>Define the abstract data type functions for explicitly sized arrays.
The explicit size is ignored and the intrinsic size of the list is used.\<close>
definition sizES :: "'el CArrPtr\<^sub>T \<Rightarrow> nat"
  where sizES_def[simp]: "sizES a \<equiv> length a"
definition vldES :: "'el CArrPtr\<^sub>T \<Rightarrow> nat \<Rightarrow> bool"
  where "vldES a i \<equiv> i < sizES a"
definition elmES :: "nat \<Rightarrow> 'el CArrPtr\<^sub>T \<Rightarrow> 'el"
  where "elmES i a \<equiv> nth a i"
definition elm_updateES :: "nat \<Rightarrow> ('el \<Rightarrow> 'el) \<Rightarrow> 'el CArrPtr\<^sub>T \<Rightarrow> 'el CArrPtr\<^sub>T"
  where "elm_updateES i f a \<equiv> (list_update a i (f (elmES i a)))"
definition elm_modifiedES :: "nat \<Rightarrow> ('el \<Rightarrow> 'el \<Rightarrow> bool) \<Rightarrow> 'el CArrPtr\<^sub>T \<Rightarrow> 'el CArrPtr\<^sub>T \<Rightarrow> bool"
  where elm_modified_def: "elm_modifiedES i m a1 a2 \<equiv> 
    m (elmES i a1) (elmES i a2) \<and> (\<forall>j \<noteq> i. vldES a1 j \<longrightarrow> elmES j a1 = elmES j a2)"
definition arr_fill_nES :: "nat \<Rightarrow> (nat \<Rightarrow> 'el) \<Rightarrow> 'el CArrPtr\<^sub>T"
  where "arr_fill_nES n f \<equiv> [f x . x \<leftarrow> [0 ..< n]]"

text \<open>Laws for the abstract data type functions\<close>
lemma vldArrES: "vldES a n = (n < length a)"
  by (simp add: vldES_def)
lemma elm_identUpdES[simp]: "elm_updateES i (\<lambda>a. a) = (\<lambda>a. a)"
  apply (unfold elm_updateES_def)
  by(simp add: elmES_def)
lemma elm_sameUpdES: "elm_updateES i (\<lambda>_. m (elmES i x)) x = elm_updateES i m x"
  by(simp add: elm_updateES_def)
thm list_update_same_conv
lemma elm_distUpdES: "vldES a i \<Longrightarrow> (elm_updateES i f) ( (elm_updateES i g) a) = elm_updateES i (f \<circ> g) a"
  for f:: "'el \<Rightarrow> 'el" and a::"'el CArrPtr\<^sub>T"
  apply (unfold elm_updateES_def elmES_def fst_def vldArrES)
  by(auto)
lemma elm_commUpd_elmES: "i < j \<Longrightarrow> (elm_updateES j m2) \<circ> (elm_updateES i m1) = (elm_updateES i m1) \<circ> (elm_updateES j m2)"
  apply (unfold elm_updateES_def elmES_def)
  apply(rule ext,simp)
  apply(rule list_update_swap)
  by(simp)
lemma elmElmUpdES: "vldES a i \<Longrightarrow> elmES i (elm_updateES i f a) = f (elmES i a)"
  by(auto simp add: elm_updateES_def elmES_def vldArrES)
lemma elmElmUpdFrameES: "vldES a i \<and> vldES a j \<and> i \<noteq> j \<Longrightarrow> elmES j (elm_updateES i f a) = elmES j a"
  by(auto simp add: elm_updateES_def elmES_def vldArrES)
lemma elmArrFillES: "i < n \<Longrightarrow> elmES i (arr_fill_nES n f) = f i"
  by(auto simp add: elmES_def arr_fill_nES_def vldArrES)
lemma sizArrFill: "sizES (arr_fill_nES n f) = n"
  by(auto simp add: arr_fill_nES_def)

text \<open>Array equality by extensionality. \<close>
lemma eqArrES: "sizES a1 = sizES a2 \<Longrightarrow>
              (a1 = a2) = 
              (\<forall> i. (vldES a1 i) \<longrightarrow> ((elmES i a1) = (elmES i a2)))"
  for a1::"'el CArrPtr\<^sub>T" and a2::"'el CArrPtr\<^sub>T"
  apply(rule iffI)
   apply(rule allI)
   apply(rule impI)
   apply(auto simp add: elmES_def vldArrES)
  apply(case_tac a1)
  apply(case_tac a2)
  apply(auto)
  apply(rule nth_equalityI)
  by(auto)

lemma eqElmUpdES: "sizES a1 = sizES a2 \<Longrightarrow> vldES a2 i \<Longrightarrow> (a1 = elm_updateES i f a2) =
                 ((elmES i a1) = f (elmES i a2) \<and> (\<forall> j. j \<noteq> i \<and> (vldES a1 j) \<longrightarrow> (elmES j a1) = (elmES j a2)))"
  apply(rule iffI)
   apply(auto)
    apply(subst elmElmUpdES,auto)
  apply(subst elmElmUpdFrameES,auto simp add: vldArrES)
  apply(subst eqArrES)
    apply(auto simp add:elm_updateES_def)
   apply(auto simp add: elmES_def)
  apply(case_tac "ia = i")
   apply(simp)
  by(auto simp add: vldArrES)
lemma eqArrFillES: "sizES a = n \<Longrightarrow> (a = arr_fill_nES n f) = 
                 ((\<forall> i. (vldES a i) \<longrightarrow> ((elmES i a) = f i)))"
  apply(rule iffI)
   apply(auto)
   apply(rule elmArrFillES)
   apply(simp add: vldArrES arr_fill_nES_def)
  apply(subst eqArrES)
   apply(simp add: vldArrES arr_fill_nES_def)
   apply(simp add: arr_fill_nES_def)
   apply(rule allI)
   apply(rule impI)
  by (auto simp add: elmES_def vldArrES)

text \<open>Semantics theorems for the Gencot array functions.\<close>

definition ctrct_getArrES :: "'el CArrES\<^sub>T \<times> ('m::len) word \<Rightarrow> bool"
  where ctrct_getArrES_def[simp]:
  "ctrct_getArrES x \<equiv> let ((a,n),i) = x in unat n = length a \<and> (unat i) < (unat n)"
theorem sem_getArrES[sem]: 
 "ctrct_getArrES (a,i) \<Longrightarrow> 
  getArrES (a,i) = elmES (unat i) (fst a)"
  by (auto simp add: getArrES_def elmES_def)

definition ctrct_setArrES :: "'el CArrES\<^sub>T \<times> ('m::len) word \<times> 'el \<Rightarrow> bool"
  where ctrct_setArrES_def[simp]:
  "ctrct_setArrES x \<equiv> let ((a,n),i,v) = x in unat n = length a \<and> (unat i) < (unat n)"
theorem sem_setArrES[sem]: 
 "ctrct_setArrES (a,i,v) \<Longrightarrow> 
  setArrES (a,i,v) = ((elm_updateES (unat i) (\<lambda>_.v) (fst a),(snd a)), ())"
  by (auto simp add: setArrES_def elm_updateES_def)

definition ctrct_modifyArrES :: "'el CArrES\<^sub>T \<times> ('m::len) word \<times> ('el \<times> 'arg \<Rightarrow> 'el \<times> 'arg) \<times> 'arg \<Rightarrow> bool"
  where ctrct_modifyArrES_def[simp]:
  "ctrct_modifyArrES x \<equiv> let ((a,n),i,f,v) = x in unat n = length a \<and> (unat i) < (unat n)"
theorem sem_modifyArrES[sem]:
 "ctrct_modifyArrES (a,i,f,x) \<Longrightarrow> 
  modifyArrES (a,i,f,x) = 
  (let (e,y) = f (elmES (unat i) (fst a), x) 
  in ((elm_updateES (unat i) (\<lambda>_.e) (fst a),(snd a)), y))"
  by (simp add: modifyArrES_def split_def Let_def elm_updateES_def elmES_def)

definition ctrct_modifyArrDfltES :: "'el CArrES\<^sub>T \<times> ('m::len) word \<times> ('el \<times> 'arg \<Rightarrow> 'el \<times> 'out) \<times> 'arg \<Rightarrow> bool"
  where ctrct_modifyArrDfltES_def[simp]:
  "ctrct_modifyArrDfltES x \<equiv> let ((a,n),i,f,v) = x in unat n = length a \<and> (unat i) < (unat n)"
theorem sem_modifyArrDfltES[sem]:
 "ctrct_modifyArrDfltES (a,i,f,x) ==> 
  modifyArrDfltES (a,i,f,x) = 
  (let (e,y) = f (elmES (unat i) (fst a), x) 
  in ((elm_updateES (unat i) (\<lambda>_.e) (fst a),(snd a)), y))"
  by (simp add: modifyArrDfltES_def split_def Let_def elm_updateES_def elmES_def)

definition ctrct_modrefArrES :: "'el CArrES\<^sub>T \<times> ('m::len) word \<times> ('pel \<times> 'arg \<Rightarrow> 'pel \<times> 'arg) \<times> 'arg \<Rightarrow> bool"
  where ctrct_modrefArrES_def[simp]:
  "ctrct_modrefArrES x \<equiv> let ((a,n),i,f,v) = x in unat n = length a \<and> (unat i) < (unat n)"
theorem sem_modrefArrES[sem]:
 "ctrct_modrefArrES (a,i,f,x) \<Longrightarrow> 
  modrefArrES (a,i,f,x) = 
  (let (e,y) = f (toPtr (elmES (unat i) (fst a)), x) 
  in ((elm_updateES (unat i) (\<lambda>_.frPtr e) (fst a),(snd a)), y))"
  by (simp add: modrefArrES_def split_def Let_def elm_updateES_def elmES_def)

definition ctrct_modrefArrDfltES :: "'el CArrES\<^sub>T \<times> ('m::len) word \<times> ('pel \<times> 'arg \<Rightarrow> 'pel \<times> 'out) \<times> 'arg \<Rightarrow> bool"
  where ctrct_modrefArrDfltES_def[simp]:
  "ctrct_modrefArrDfltES x \<equiv> let ((a,n),i,f,v) = x in unat n = length a \<and> (unat i) < (unat n)"
theorem sem_modrefArrDfltES[sem]:
 "ctrct_modrefArrDfltES (a,i,f,x) ==> 
  modrefArrDfltES (a,i,f,x) = 
  (let (e,y) = f (toPtr (elmES (unat i) (fst a)), x) 
  in ((elm_updateES (unat i) (\<lambda>_.frPtr e) (fst a),(snd a)), y))"
  by (simp add: modrefArrDfltES_def split_def Let_def elm_updateES_def elmES_def)

end
