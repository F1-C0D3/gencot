theory Gencot_CArray
  imports ShallowShared
    Gencot_Default
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

definition modifyArr' :: "('n::len, 'el) FixedList \<Rightarrow> 'idx::len word \<Rightarrow> (('el, 'arg) RR \<Rightarrow> ('el, 'arg) RR) \<Rightarrow> 'arg \<Rightarrow> (('n, 'el) FixedList, 'arg) RR"
  where
    "modifyArr' lst idx chf inp \<equiv> 
      if unat idx >= LENGTH('n) then RR.make lst inp
      else let l = Rep_FixedList lst; elm = nth l (unat idx); chres = chf(RR.make elm inp)
        in RR.make (Abs_FixedList (list_update l (unat idx) (RR.p1\<^sub>f chres))) (RR.p2\<^sub>f chres)"

definition modifyArrDflt' :: "('n::len, 'el) FixedList \<Rightarrow> 'idx::len word \<Rightarrow>(('el, 'arg) RR \<Rightarrow> ('el, 'out) RR) \<Rightarrow> 'arg \<Rightarrow> (('n, 'el) FixedList, 'out) RR"
  where
    "modifyArrDflt' lst idx chf inp \<equiv> 
      if unat idx >= LENGTH('n) then RR.make lst (defaultVal ())
      else let l = Rep_FixedList lst; elm = nth l (unat idx); chres = chf(RR.make elm inp)
        in RR.make (Abs_FixedList (list_update l (unat idx) (RR.p1\<^sub>f chres))) (RR.p2\<^sub>f chres)"

text \<open>
  This locale has the wrapper record access and constructor as parameters.
  It defines the array functions for the wrapper record and proves some useful lemmas.\<close>

locale CArrFuns = 
  fixes 
    fld :: "'arr \<Rightarrow> ('n::len, 'el) FixedList" and 
    wrp :: "('n, 'el) FixedList \<Rightarrow> 'arr" 
begin
definition getArrFxd :: "('arr, 32 word) RR \<Rightarrow> 'el"
  where "getArrFxd arg \<equiv>
  let arr = RR.p1\<^sub>f arg; idx = RR.p2\<^sub>f arg 
  in getArr' (fld arr) idx"
definition setArrFxd :: "('arr, (32 word, 'el) RR) RR \<Rightarrow> ('arr, unit) RR"
  where "setArrFxd arg \<equiv>
  let arr = RR.p1\<^sub>f arg; idx = RR.p1\<^sub>f (RR.p2\<^sub>f arg); elm = RR.p2\<^sub>f (RR.p2\<^sub>f arg) 
  in RR.make (wrp(setArr' (fld arr) idx elm)) ()"
definition modifyArrFxd :: "('arr, (32 word, ('el, 'arg) RR \<Rightarrow> ('el, 'arg) RR, 'arg) Tup3) RR \<Rightarrow> ('arr, 'arg) RR"
  where "modifyArrFxd arg \<equiv>
  let arr = RR.p1\<^sub>f arg; idx = Tup3.p1\<^sub>f (RR.p2\<^sub>f arg); chf = Tup3.p2\<^sub>f (RR.p2\<^sub>f arg); inp = Tup3.p3\<^sub>f (RR.p2\<^sub>f arg); fres = modifyArr' (fld arr) idx chf inp 
  in RR.make (wrp (RR.p1\<^sub>f fres)) (RR.p2\<^sub>f fres)"
definition modifyArrDfltFxd :: "('arr, (32 word, ('el, 'arg) RR \<Rightarrow> ('el, 'out) RR, 'arg) Tup3) RR \<Rightarrow> ('arr, 'out) RR"
  where "modifyArrDfltFxd arg \<equiv>
  let arr = RR.p1\<^sub>f arg; idx = Tup3.p1\<^sub>f (RR.p2\<^sub>f arg); chf = Tup3.p2\<^sub>f (RR.p2\<^sub>f arg); inp = Tup3.p3\<^sub>f (RR.p2\<^sub>f arg); fres = modifyArrDflt' (fld arr) idx chf inp
  in RR.make (wrp (RR.p1\<^sub>f fres)) (RR.p2\<^sub>f fres)"

end

end
