theory Gencot_CArray_Tuples
  imports ShallowShared_Tuples
    Gencot_Default_Tuples
begin

text \<open>Define the array functions for fixed lists\<close>

definition getArr' :: "('n::len, 'el) FixedList \<Rightarrow> 'idx::len word \<Rightarrow> 'el"
  where 
    "getArr' lst idx \<equiv>
      if unat idx >= LENGTH('n) then hd (Rep_FixedList lst)
      else (nth (Rep_FixedList lst) (unat idx))"

definition setArr' :: "('n::len, 'el) FixedList \<Rightarrow> 'idx::len word \<Rightarrow> 'el \<Rightarrow> ('n, 'el) FixedList"
  where
    "setArr' lst idx elm \<equiv> 
      if unat idx >= LENGTH('n) then lst
      else (Abs_FixedList (list_update (Rep_FixedList lst) (unat idx) elm))"

definition modifyArr' :: "('n::len, 'el) FixedList \<Rightarrow> 'idx::len word \<Rightarrow> ('el \<times> 'arg \<Rightarrow> 'el \<times> 'arg) \<Rightarrow> 'arg \<Rightarrow> ('n, 'el) FixedList \<times> 'arg"
  where
    "modifyArr' lst idx chf inp \<equiv> 
      if unat idx >= LENGTH('n) then (lst, inp)
      else let l = Rep_FixedList lst; elm = nth l (unat idx); chres = chf(elm, inp)
        in (Abs_FixedList (list_update l (unat idx) (fst chres)), snd chres)"

definition modifyArrDflt' :: "('n::len, 'el) FixedList \<Rightarrow> 'idx::len word \<Rightarrow> ('el \<times> 'arg \<Rightarrow> 'el \<times> 'out) \<Rightarrow> 'arg \<Rightarrow> ('n, 'el) FixedList \<times> 'out"
  where
    "modifyArrDflt' lst idx chf inp \<equiv> 
      if unat idx >= LENGTH('n) then (lst, defaultVal ())
      else let l = Rep_FixedList lst; elm = nth l (unat idx); chres = chf(elm, inp)
        in (Abs_FixedList (list_update l (unat idx) (fst chres)), snd chres)"

text \<open>Lift arrays to the wrapper records.
      We introduce an overloaded abstract data type for all such arrays with indexes of type nat.
      It consists of the following functions.
      Array accesses are always guarded by function vld.\<close>
consts 
  siz :: "'arr \<Rightarrow> nat"
  vld :: "'arr \<Rightarrow> nat \<Rightarrow> bool"
  elm :: "'arr \<Rightarrow> nat \<Rightarrow> 'el"
  upd :: "'arr \<Rightarrow> nat \<Rightarrow> 'el \<Rightarrow> 'arr"

text \<open>For every actual wrapper record the following locale will be interpreted.
      It takes the wrapper record access and constructor as parameters.
      The locale defines the laws of the abstract data type, 
      specific array functions for the wrapper record and their conversion to the abstract data type functions.\<close>

locale CArrFuns = 
  fixes 
    fld :: "'arr \<Rightarrow> ('n::len, 'el) FixedList" and 
    wrp :: "('n, 'el) FixedList \<Rightarrow> 'arr"
  assumes 
    fld_inverse: "\<And>x. wrp (fld x) = x" and 
    wrp_inverse: "\<And>x. fld (wrp x) = x" 
begin
text \<open>Lift the array functions from fixed lists to the wrapper record.\<close>
definition getArrFxd :: "'arr \<times> ('m::len) word \<Rightarrow> 'el"
  where "getArrFxd arg \<equiv> let (arr,idx) = arg in getArr' (fld arr) idx"
definition setArrFxd :: "'arr \<times> ('m::len) word \<times> 'el \<Rightarrow> 'arr \<times> unit"
  where "setArrFxd arg \<equiv> let (arr,idx,elm) = arg in (wrp(setArr' (fld arr) idx elm), ())"
definition modifyArrFxd :: "'arr \<times> ('m::len) word \<times> ('el \<times> 'arg \<Rightarrow> 'el \<times> 'arg) \<times> 'arg \<Rightarrow> 'arr \<times> 'arg"
  where "modifyArrFxd arg \<equiv> let (arr, idx, chf, inp) = arg; 
    (reslst,res) = modifyArr' (fld arr) idx chf inp in (wrp reslst, res)"
definition modifyArrDfltFxd :: "'arr \<times> ('m::len) word \<times> ('el \<times> 'arg \<Rightarrow> 'el \<times> 'out) \<times> 'arg \<Rightarrow> 'arr \<times> 'out"
  where "modifyArrDfltFxd arg \<equiv> let (arr, idx, chf, inp) = arg;
    (reslst,res) = modifyArrDflt' (fld arr) idx chf inp in (wrp reslst, res)"

text \<open>Define conversion functions between lists and the wrapper record.\<close>
definition lstFxd :: "'arr \<Rightarrow> 'el list"
  where "lstFxd a \<equiv> Rep_FixedList (fld a)"
definition arrFxd :: "'el list \<Rightarrow> 'arr"
  where "arrFxd a \<equiv> wrp (Abs_FixedList a)"

text \<open>Define the abstract data type functions for the wrapper record.\<close>
definition sizFxd :: "'arr \<Rightarrow> nat"
  where "sizFxd a \<equiv> length (lstFxd a)"
definition vldFxd :: "'arr => nat => bool"
  where "vldFxd a i \<equiv> i < sizFxd a"
definition elmFxd :: "'arr \<Rightarrow> nat \<Rightarrow> 'el"
  where "elmFxd a i \<equiv> nth (lstFxd a) i"
definition updFxd :: "'arr \<Rightarrow> nat \<Rightarrow> 'el \<Rightarrow> 'arr"
  where "updFxd a i e \<equiv> arrFxd (list_update (lstFxd a) i e)"

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
lemma updArr: "vldFxd a i \<Longrightarrow> elmFxd (updFxd a i e) i = e"
  apply(auto simp add: updFxd_def elmFxd_def lstFxd_def arrFxd_def wrp_inverse vldArr)
  apply(subst Abs_FixedList_inverse)
  apply(cut_tac x = "(fld a)" in Rep_FixedList )
  apply(auto)
  apply(cut_tac x = "(fld a)" in Rep_FixedList )
  by auto
lemma updArrFrame: "vldFxd a i \<and> vldFxd a j \<and> i \<noteq> j \<Longrightarrow> elmFxd (updFxd a i e) j = elmFxd a j"
  apply(auto simp add: updFxd_def elmFxd_def lstFxd_def arrFxd_def wrp_inverse vldArr)
  apply(subst Abs_FixedList_inverse)
  apply(cut_tac x = "(fld a)" in Rep_FixedList )
  by (auto)

text \<open>Array equality by extensionality. \<close>
lemma eqArr1: "(\<And> i. (vldFxd a1 i) \<Longrightarrow> ((elmFxd a1 i) = (elmFxd a2 i))) \<Longrightarrow> (a1 = a2)"
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
lemma eqArr: "(a1 = a2) = (\<forall> i. (vldFxd a1 i) \<longrightarrow> ((elmFxd a1 i) = (elmFxd a2 i)))"
  apply(rule iffI)
   apply(rule allI)
   apply(rule impI)
   apply(auto)
  by (rule eqArr1,auto)

text \<open>Conversion laws for the array functions to the abstract data type.\<close>
text \<open>Conversion for getArr\<close>
lemma getArrValid: "vldFxd a (unat i) \<Longrightarrow> getArrFxd (a,i) = elmFxd a (unat i)"
  by (simp add: getArrFxd_def getArr'_def vldArr elmFxd_def lstFxd_def)
lemma getArrInvalid: "\<not> vldFxd a (unat i) \<Longrightarrow> getArrFxd (a,i) = elmFxd a 0"
  apply(simp add: getArrFxd_def getArr'_def vldArr elmFxd_def)
  apply(fold lstFxd_def)
  apply(case_tac " lstFxd a")
   apply(cut_tac arrNotNil)
  by auto

text \<open>Conversion for setArr\<close>
lemma setArrValid: "vldFxd a (unat i) \<Longrightarrow> setArrFxd (a,i,v) = (updFxd a (unat i) v, ())"
  by (simp add: setArrFxd_def setArr'_def vldArr lstFxd_def arrFxd_def updFxd_def)
lemma setArrInvalid: "\<not> vldFxd a (unat i) \<Longrightarrow> setArrFxd (a,i,v) = (a,())"
  by (simp add: setArrFxd_def setArr'_def vldArr fld_inverse)

text \<open>Conversion for modifyArr\<close>
lemma modifyArrValid: "vldFxd a (unat i) \<Longrightarrow> modifyArrFxd (a,i,f,x) = (let (e,y) = f (elmFxd a (unat i), x) in (updFxd a (unat i) e, y))"
  by (simp add: modifyArrFxd_def modifyArr'_def split_def Let_def vldArr lstFxd_def arrFxd_def updFxd_def elmFxd_def)
lemma modifyArrInvalid: "\<not> (vldFxd a (unat i))  ==> modifyArrFxd (a,i,f,x) = (a, x)"
  by (simp add: modifyArrFxd_def modifyArr'_def vldArr fld_inverse)

text \<open>Conversion for modifyArrDfl\<close>
lemma modifyArrDfltValid: "vldFxd a (unat i)   ==> modifyArrDfltFxd (a,i,f,x) = (let (e,y) = f (elmFxd a (unat i), x) in (updFxd a (unat i) e, y))"
  by (simp add: modifyArrDfltFxd_def modifyArrDflt'_def split_def Let_def vldArr lstFxd_def arrFxd_def updFxd_def elmFxd_def)
lemma modifyArrDfltInvalid: "\<not> (vldFxd a (unat i))  ==> modifyArrDfltFxd (a,i,f,x) = (a, defaultVal ())"
  by (simp add: modifyArrDfltFxd_def modifyArrDflt'_def vldArr fld_inverse)

end

end
