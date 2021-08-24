theory Gencot_CArray_Lemmas
  imports "Gencot_CArray_Tuples"
begin

text \<open>Lift arrays to the wrapper records.
      We introduce an overloaded abstract data type for all such arrays with indexes of type nat.
      It consists of the following functions.
      Array accesses are always guarded by function vld.\<close>
consts 
  arr :: "'el list \<Rightarrow> 'arr"
  siz :: "'arr \<Rightarrow> nat"
  vld :: "'arr \<Rightarrow> nat \<Rightarrow> bool"
  elm :: "nat \<Rightarrow> 'arr \<Rightarrow> 'el"
  elm_update :: "nat \<Rightarrow> ('el \<Rightarrow> 'el) \<Rightarrow> 'arr \<Rightarrow> 'arr"
  elm_modified :: "nat \<Rightarrow> ('el \<Rightarrow> 'el \<Rightarrow> bool) \<Rightarrow> 'arr \<Rightarrow> 'arr \<Rightarrow> bool"
  arr_fill :: "(nat \<Rightarrow> 'el) \<Rightarrow> 'arr"

text \<open>For every actual wrapper record the following locale will be interpreted.
      It extends CArrFuns by the laws of the abstract data type, 
      and conversion from the Gencot array functions to the abstract data type functions.\<close>

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
  where "lstFxd a \<equiv> Rep_FixedList (fld a)"
definition arrFxd :: "'el list \<Rightarrow> 'arr"
  where "arrFxd a \<equiv> wrp (Abs_FixedList a)"

text \<open>Define the abstract data type functions for the wrapper record.\<close>
definition sizFxd :: "'arr \<Rightarrow> nat"
  where "sizFxd a \<equiv> length (lstFxd a)"
definition vldFxd :: "'arr \<Rightarrow> nat \<Rightarrow> bool"
  where "vldFxd a i \<equiv> i < sizFxd a"
definition elmFxd :: "nat \<Rightarrow> 'arr \<Rightarrow> 'el"
  where "elmFxd i a \<equiv> nth (lstFxd a) i"
definition elm_updateFxd :: "nat \<Rightarrow> ('el \<Rightarrow> 'el) \<Rightarrow> 'arr \<Rightarrow> 'arr"
  where "elm_updateFxd i f a \<equiv> arrFxd (list_update (lstFxd a) i (f (elmFxd i a)))"
definition elm_modifiedFxd :: "nat \<Rightarrow> ('el \<Rightarrow> 'el \<Rightarrow> bool) \<Rightarrow> 'arr \<Rightarrow> 'arr \<Rightarrow> bool"
  where elm_modified_def: "elm_modifiedFxd i m a1 a2 \<equiv> 
    m (elmFxd i a1) (elmFxd i a2) \<and> (\<forall>j \<noteq> i. vldFxd a1 j \<longrightarrow> elmFxd j a1 = elmFxd j a2)"
definition arr_fillFxd :: "(nat \<Rightarrow> 'el) \<Rightarrow> 'arr"
  where "arr_fillFxd f \<equiv> arrFxd [f x . x \<leftarrow> [0 ..< LENGTH('n)]]"

text \<open>Arrays are never empty.\<close>
lemma arrNotNil: "\<forall>x::'arr .  lstFxd x \<noteq> []"
  apply(rule allI)
  apply(unfold lstFxd_def)
  apply(cut_tac x = "(fld x)" in Rep_FixedList )
  by auto

text \<open>Laws for the abstract data type functions\<close>
lemma sizArr: "sizFxd a = LENGTH('n)"
  apply(unfold sizFxd_def lstFxd_def)
  by (simp add: length_FixedList)
lemma vldArr: "vldFxd a n = (n < LENGTH('n))"
  by (simp add: vldFxd_def sizArr)
lemma elm_identUpd[simp]: "elm_updateFxd i (\<lambda>a. a) = (\<lambda>a. a)"
  apply (unfold elm_updateFxd_def)
  by(simp add: elmFxd_def arrFxd_def lstFxd_def Rep_FixedList_inverse fld_inverse)
lemma elm_sameUpd: "elm_updateFxd i (\<lambda>_. m (elmFxd i x)) x = elm_updateFxd i m x"
  by(simp add: elm_updateFxd_def)
lemma elm_distUpd: "(i < LENGTH('n)) \<Longrightarrow> (elm_updateFxd i f) \<circ> (elm_updateFxd i g) = elm_updateFxd i (f \<circ> g)"
  for f:: "'el \<Rightarrow> 'el"
  apply (unfold elm_updateFxd_def elmFxd_def arrFxd_def lstFxd_def)
  apply(rule ext,simp)
  apply(cut_tac x = "(fld a)" in Rep_FixedList )
  apply(subst wrp_inverse)+
  apply(subst Abs_FixedList_inverse,simp)+
  by(auto)
lemma elm_commUpd_elm: "i < j \<Longrightarrow> (elm_updateFxd j m2) \<circ> (elm_updateFxd i m1) = (elm_updateFxd i m1) \<circ> (elm_updateFxd j m2)"
  apply (unfold elm_updateFxd_def elmFxd_def arrFxd_def lstFxd_def)
  apply(rule ext,simp)
  apply(cut_tac x = "(fld x)" in Rep_FixedList )
  apply(subst wrp_inverse)+
  apply(subst Abs_FixedList_inverse,simp)+
  apply (simp)
  apply(rule arg_cong[where f=wrp])
  apply(rule arg_cong[where f=Abs_FixedList])
  apply(rule list_update_swap)
  by(simp)
lemma elmElmUpd: "vldFxd a i \<Longrightarrow> elmFxd i (elm_updateFxd i f a) = f (elmFxd i a)"
  apply(auto simp add: elm_updateFxd_def elmFxd_def arrFxd_def lstFxd_def vldArr)
  apply(cut_tac x = "(fld a)" in Rep_FixedList )
  apply(subst wrp_inverse)
  apply(subst Abs_FixedList_inverse)
  by (auto)
lemma elmElmUpdFrame: "vldFxd a i \<and> vldFxd a j \<and> i \<noteq> j \<Longrightarrow> elmFxd j (elm_updateFxd i f a) = elmFxd j a"
  apply(auto simp add: elm_updateFxd_def elmFxd_def arrFxd_def lstFxd_def vldArr)
  apply(cut_tac x = "(fld a)" in Rep_FixedList )
  apply(subst wrp_inverse)
  apply(subst Abs_FixedList_inverse)
  by (auto)
lemma elmArrFill: "i < LENGTH('n) \<Longrightarrow> elmFxd i (arr_fillFxd f) = f i"
  apply(auto simp add: elmFxd_def arr_fillFxd_def lstFxd_def arrFxd_def wrp_inverse vldArr sizArr)
  apply(subst Abs_FixedList_inverse)
  by auto

text \<open>Array equality by extensionality. \<close>
lemma eqArr1: "(\<And> i. (vldFxd a1 i) \<Longrightarrow> ((elmFxd i a1) = (elmFxd i a2))) \<Longrightarrow> (a1 = a2)"
  apply(auto simp add: elmFxd_def vldFxd_def sizFxd_def lstFxd_def)
  apply(drule nth_equalityI[rotated])
  apply(cut_tac x = "(fld a1)" in Rep_FixedList )
  apply(cut_tac x = "(fld a2)" in Rep_FixedList )
  apply(simp)
  apply(drule arg_cong[where f = Abs_FixedList])
  apply(subst (asm) Rep_FixedList_inverse)+
  apply(drule arg_cong[where f = wrp])
  apply(simp add: fld_inverse)
  done
lemma eqArr: "(a1 = a2) = 
              (\<forall> i. (vldFxd a1 i) \<longrightarrow> ((elmFxd i a1) = (elmFxd i a2)))"
  apply(rule iffI)
   apply(rule allI)
   apply(rule impI)
   apply(auto)
  by (rule eqArr1,auto)

lemma eqElmUpd: "vldFxd a2 i \<Longrightarrow> (a1 = elm_updateFxd i f a2) =
                 ((elmFxd i a1) = f (elmFxd i a2) \<and> (\<forall> j. j \<noteq> i \<and> (vldFxd a1 j) \<longrightarrow> (elmFxd j a1) = (elmFxd j a2)))"
  apply(rule iffI)
   apply(auto)
    apply(subst elmElmUpd,auto)
  apply(subst elmElmUpdFrame,auto simp add: vldArr)
  apply(subst eqArr)
   apply(rule allI)
  apply(rule impI)
  apply(case_tac "ia = i")
  apply(simp)
   apply(subst elmElmUpd,auto simp add: vldArr)
  apply(subst elmElmUpdFrame,auto simp add: vldArr)
  done

lemma eqArrFill: "(a = arr_fillFxd f) = 
                 ((\<forall> i. (vldFxd a i) \<longrightarrow> ((elmFxd i a) = f i)))"
  apply(rule iffI)
   apply(auto)
   apply(rule elmArrFill)
   apply(simp add: vldArr)
  apply(subst eqArr)
   apply(rule allI)
   apply(rule impI)
  apply(subst elmArrFill)
  by (auto simp add: vldArr)

text \<open>Semantics theorems for the Gencot array functions.\<close>

definition ctrct_getArrFxd :: "'arr \<times> ('m::len) word \<Rightarrow> bool"
  where ctrct_getArrFxd_def[simp]:
  "ctrct_getArrFxd x \<equiv> let (a,i) = x in vldFxd a (unat i)"
theorem sem_getArr: 
 "ctrct_getArrFxd (a,i) \<Longrightarrow> 
  getArrFxd (a,i) = elmFxd (unat i) a"
  by (simp add: getArrFxd_def getArr'_def vldArr elmFxd_def lstFxd_def)
theorem errsem_getArr:
 "\<not> ctrct_getArrFxd (a,i) \<Longrightarrow> 
  getArrFxd (a,i) = elmFxd 0 a"
  apply(simp add: getArrFxd_def getArr'_def vldArr elmFxd_def)
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
  by (simp add: setArrFxd_def setArr'_def vldArr lstFxd_def arrFxd_def elm_updateFxd_def)
theorem errsem_setArr:
 "\<not> ctrct_setArrFxd (a,i,v) \<Longrightarrow> 
  setArrFxd (a,i,v) = (a,())"
  by (simp add: setArrFxd_def setArr'_def vldArr fld_inverse)

definition ctrct_modifyArrFxd :: "'arr \<times> ('m::len) word \<times> ('el \<times> 'arg \<Rightarrow> 'el \<times> 'arg) \<times> 'arg \<Rightarrow> bool"
  where ctrct_modifyArrFxd_def[simp]:
  "ctrct_modifyArrFxd x \<equiv> let (a,i,f,v) = x in vldFxd a (unat i)"
theorem sem_modifyArr:
 "ctrct_modifyArrFxd (a,i,f,x) \<Longrightarrow> 
  modifyArrFxd (a,i,f,x) = 
  (let (e,y) = f (elmFxd (unat i) a, x) in (elm_updateFxd (unat i) (\<lambda>_.e) a, y))"
  by (simp add: modifyArrFxd_def modifyArr'_def split_def Let_def vldArr lstFxd_def arrFxd_def elm_updateFxd_def elmFxd_def)
theorem errsem_modifyArr:
 "\<not> ctrct_modifyArrFxd (a,i,f,x) ==> 
  modifyArrFxd (a,i,f,x) = (a, x)"
  by (simp add: modifyArrFxd_def modifyArr'_def vldArr fld_inverse)

definition ctrct_modifyArrDfltFxd :: "'arr \<times> ('m::len) word \<times> ('el \<times> 'arg \<Rightarrow> 'el \<times> 'out) \<times> 'arg \<Rightarrow> bool"
  where ctrct_modifyArrDfltFxd_def[simp]:
  "ctrct_modifyArrDfltFxd x \<equiv> let (a,i,f,v) = x in vldFxd a (unat i)"
theorem sem_modifyArrDflt:
 "ctrct_modifyArrDfltFxd (a,i,f,x) ==> 
  modifyArrDfltFxd (a,i,f,x) = 
  (let (e,y) = f (elmFxd (unat i) a, x) in (elm_updateFxd (unat i) (\<lambda>_.e) a, y))"
  by (simp add: modifyArrDfltFxd_def modifyArrDflt'_def split_def Let_def vldArr lstFxd_def arrFxd_def elm_updateFxd_def elmFxd_def)
theorem errsem_modifyArrDflt:
 "\<not> ctrct_modifyArrDfltFxd (a,i,f,x) ==>
  modifyArrDfltFxd (a,i,f,x) = (a, defaultVal ())"
  by (simp add: modifyArrDfltFxd_def modifyArrDflt'_def vldArr fld_inverse)

definition ctrct_modrefArrFxd :: "'arr \<times> ('m::len) word \<times> ('pel \<times> 'arg \<Rightarrow> 'pel \<times> 'arg) \<times> 'arg \<Rightarrow> bool"
  where ctrct_modrefArrFxd_def[simp]:
  "ctrct_modrefArrFxd x \<equiv> let (a,i,f,v) = x in vldFxd a (unat i)"
theorem sem_modrefArr:
 "ctrct_modrefArrFxd (a,i,f,x) \<Longrightarrow> 
  modrefArrFxd (a,i,f,x) = 
  (let (e,y) = f (toPtr (elmFxd (unat i) a), x) in (elm_updateFxd (unat i) (\<lambda>_.frPtr e) a, y))"
  by (simp add: modrefArrFxd_def modrefArr'_def split_def Let_def vldArr lstFxd_def arrFxd_def elm_updateFxd_def elmFxd_def)
theorem errsem_modrefArr:
 "\<not> ctrct_modrefArrFxd (a,i,f,x) ==> 
  modrefArrFxd (a,i,f,x) = (a, x)"
  by (simp add: modrefArrFxd_def modrefArr'_def vldArr fld_inverse)

definition ctrct_modrefArrDfltFxd :: "'arr \<times> ('m::len) word \<times> ('pel \<times> 'arg \<Rightarrow> 'pel \<times> 'out) \<times> 'arg \<Rightarrow> bool"
  where ctrct_modrefArrDfltFxd_def[simp]:
  "ctrct_modrefArrDfltFxd x \<equiv> let (a,i,f,v) = x in vldFxd a (unat i)"
theorem sem_modrefArrDflt:
 "ctrct_modrefArrDfltFxd (a,i,f,x) ==> 
  modrefArrDfltFxd (a,i,f,x) = 
  (let (e,y) = f (toPtr (elmFxd (unat i) a), x) in (elm_updateFxd (unat i) (\<lambda>_.frPtr e) a, y))"
  by (simp add: modrefArrDfltFxd_def modrefArrDflt'_def split_def Let_def vldArr lstFxd_def arrFxd_def elm_updateFxd_def elmFxd_def)
theorem errsem_modrefArrDflt:
 "\<not> ctrct_modrefArrDfltFxd (a,i,f,x) ==>
  modrefArrDfltFxd (a,i,f,x) = (a, defaultVal ())"
  by (simp add: modrefArrDfltFxd_def modrefArrDflt'_def vldArr fld_inverse)

end

end
