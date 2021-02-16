theory Gencot_CArray_Tuples
  imports ShallowShared_Tuples
    Gencot_Default_Tuples
begin

text \<open>First we define the array functions for fixed lists\<close>

definition getArr' :: "('n::finite, 'el) FixedList \<Rightarrow> 32 word \<Rightarrow> 'el"
  where 
    "getArr' lst idx \<equiv>
      if unat idx >= CARD('n) then hd (Rep_FixedList lst)
      else (nth (Rep_FixedList lst) (unat idx))"

definition setArr' :: "('n::finite, 'el) FixedList \<Rightarrow> 32 word \<Rightarrow> 'el \<Rightarrow> ('n, 'el) FixedList"
  where
    "setArr' lst idx elm \<equiv> 
      if unat idx >= CARD('n) then lst
      else (Abs_FixedList (list_update (Rep_FixedList lst) (unat idx) elm))"

definition modifyArr' :: "('n::finite, 'el) FixedList \<Rightarrow> 32 word \<Rightarrow> ('el \<times> 'arg \<Rightarrow> 'el \<times> 'arg) \<Rightarrow> 'arg \<Rightarrow> ('n, 'el) FixedList \<times> 'arg"
  where
    "modifyArr' lst idx chf inp \<equiv> 
      if unat idx >= CARD('n) then (lst, inp)
      else let l = Rep_FixedList lst; elm = nth l (unat idx); chres = chf(elm, inp)
        in (Abs_FixedList (list_update l (unat idx) (fst chres)), snd chres)"

definition modifyArrDflt' :: "('n::finite, 'el) FixedList \<Rightarrow> 32 word \<Rightarrow> ('el \<times> 'arg \<Rightarrow> 'el \<times> 'out) \<Rightarrow> 'arg \<Rightarrow> ('n, 'el) FixedList \<times> 'out"
  where
    "modifyArrDflt' lst idx chf inp \<equiv> 
      if unat idx >= CARD('n) then (lst, defaultVal ())
      else let l = Rep_FixedList lst; elm = nth l (unat idx); chres = chf(elm, inp)
        in (Abs_FixedList (list_update l (unat idx) (fst chres)), snd chres)"

text \<open>
  This locale has the wrapper record access and constructor as parameters.
  It defines the array functions for the wrapper record and proves some useful lemmas.\<close>

locale CArrFuns = fixes fld :: "'arr \<Rightarrow> ('n::finite, 'el) FixedList" and wrp :: "('n, 'el) FixedList \<Rightarrow> 'arr"
begin
definition getArrFxd :: "'arr \<times> 32 word \<Rightarrow> 'el"
  where "getArrFxd arg \<equiv> let (arr,idx) = arg in getArr' (fld arr) idx"
definition setArrFxd :: "'arr \<times> 32 word \<times> 'el \<Rightarrow> 'arr \<times> unit"
  where "setArrFxd arg \<equiv> let (arr,idx,elm) = arg in (wrp(setArr' (fld arr) idx elm), ())"
definition modifyArrFxd :: "'arr \<times> 32 word \<times> ('el \<times> 'arg \<Rightarrow> 'el \<times> 'arg) \<times> 'arg \<Rightarrow> 'arr \<times> 'arg"
  where "modifyArrFxd arg \<equiv> let (arr, idx, chf, inp) = arg; 
    (reslst,res) = modifyArr' (fld arr) idx chf inp in (wrp reslst, res)"
definition modifyArrDfltFxd :: "'arr \<times> 32 word \<times> ('el \<times> 'arg \<Rightarrow> 'el \<times> 'out) \<times> 'arg \<Rightarrow> 'arr \<times> 'out"
  where "modifyArrDfltFxd arg \<equiv> let (arr, idx, chf, inp) = arg;
    (reslst,res) = modifyArrDflt' (fld arr) idx chf inp in (wrp reslst, res)"

text \<open>Arrays are never empty.\<close>
lemma arrNotNil: "\<forall>x::'arr .  (Rep_FixedList (fld  x)) \<noteq> []"
  apply(rule allI)
  apply(cut_tac x = "(fld (x::'arr))" for el in Rep_FixedList )
  apply(auto)
  done
end

end
