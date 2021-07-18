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

text \<open>For every actual wrapper record the following locale will be interpreted.
      It takes the wrapper record access and constructor as parameters.
      The locale defines specific array functions for the wrapper record.\<close>

locale CArrFuns = 
  fixes 
    fld :: "'arr \<Rightarrow> ('n::len, 'el) FixedList" and 
    wrp :: "('n, 'el) FixedList \<Rightarrow> 'arr"
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

end

end
