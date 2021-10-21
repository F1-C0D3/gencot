theory Gencot_CArray_Tuples
  imports ShallowShared_Tuples
    Gencot_Default_Tuples
  "HOL-Library.Adhoc_Overloading"
begin

text \<open>Declare pointer referencing / dereferencing functions for modrefArr.
These must be overloaded for every type which occurs as element type of an array.\<close>

consts
  toPtr :: "'el \<Rightarrow> 'pel"
  frPtr :: "'pel \<Rightarrow> 'el"

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

definition modifyArr' :: "('n::len, 'el) FixedList \<Rightarrow> 'idx::len word \<Rightarrow> ('el \<times> 'arg \<Rightarrow> 'el \<times> 'out) \<Rightarrow> 'arg \<Rightarrow> ('n, 'el) FixedList \<times> 'out"
  where
    "modifyArr' lst idx chf inp \<equiv> 
      let i = (if unat idx >= LENGTH('n) then 0 else unat idx); 
          l = Rep_FixedList lst; elm = nth l i; chres = chf(elm, inp)
      in (Abs_FixedList (list_update l i (fst chres)), snd chres)"

definition modrefArr' :: "('n::len, 'el) FixedList \<Rightarrow> 'idx::len word \<Rightarrow> ('pel \<times> 'arg \<Rightarrow> 'pel \<times> 'out) \<Rightarrow> 'arg \<Rightarrow> ('n, 'el) FixedList \<times> 'out"
  where
    "modrefArr' lst idx chf inp \<equiv> 
      let i = (if unat idx >= LENGTH('n) then 0 else unat idx); 
          l = Rep_FixedList lst; elm = nth l i; chres = chf(toPtr elm, inp)
      in (Abs_FixedList (list_update l i (frPtr (fst chres))), snd chres)"

definition toCAES' :: "('n::len, 'el) FixedList \<Rightarrow> 'el CArrES\<^sub>T"
  where "toCAES' lst \<equiv> (Rep_FixedList lst, of_nat LENGTH('n))"

definition fromCAES' :: "'el CArrES\<^sub>T \<Rightarrow> ('n::len, 'el) FixedList"
  where "fromCAES' aes \<equiv> Abs_FixedList (fst aes) "

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
definition modifyArrFxd :: "'arr \<times> ('m::len) word \<times> ('el \<times> 'arg \<Rightarrow> 'el \<times> 'out) \<times> 'arg \<Rightarrow> 'arr \<times> 'out"
  where "modifyArrFxd arg \<equiv> let (arr, idx, chf, inp) = arg; 
    (reslst,res) = modifyArr' (fld arr) idx chf inp in (wrp reslst, res)"
definition modrefArrFxd :: "'arr \<times> ('m::len) word \<times> ('pel \<times> 'arg \<Rightarrow> 'pel \<times> 'out) \<times> 'arg \<Rightarrow> 'arr \<times> 'out"
  where "modrefArrFxd arg \<equiv> let (arr, idx, chf, inp) = arg; 
    (reslst,res) = modrefArr' (fld arr) idx chf inp in (wrp reslst, res)"

definition toCAESFxd :: "'arr \<Rightarrow> 'el CArrES\<^sub>T"
  where "toCAESFxd arr \<equiv> toCAES' (fld arr)"
definition fromCAESFxd :: "'el CArrES\<^sub>T \<Rightarrow> 'arr"
  where "fromCAESFxd aes \<equiv> wrp (fromCAES' aes)"
definition rotoCAESFxd :: "'arr \<Rightarrow> 'el CArrES\<^sub>T"
  where "rotoCAESFxd arr \<equiv> toCAES' (fld arr)"
definition rofromCAESFxd :: "'el CArrES\<^sub>T \<Rightarrow> 'arr"
  where "rofromCAESFxd aes \<equiv> wrp (fromCAES' aes)"

end

text \<open>Define the array functions for explicitly sized arrays\<close>

definition getArrES :: "'el CArrES\<^sub>T \<times> 'idx::len word \<Rightarrow> 'el"
  where 
    "getArrES arg \<equiv>
      let ((lst,len),idx) = arg
      in if unat idx >= unat len then hd lst
         else (nth lst (unat idx))"

definition setArrES :: "'el CArrES\<^sub>T \<times> 'idx::len word \<times> 'el \<Rightarrow> 'el CArrES\<^sub>T \<times> unit"
  where
    "setArrES arg \<equiv> 
      let ((lst,len),idx,elm) = arg
      in if unat idx >= unat len then ((lst,len),())
         else (((list_update lst (unat idx) elm),len),())"

definition modifyArrES :: "'el CArrES\<^sub>T \<times> ('idx::len word \<times> ('el \<times> 'arg \<Rightarrow> 'el \<times> 'out) \<times> 'arg) \<Rightarrow> 'el CArrES\<^sub>T \<times> 'out"
  where
    "modifyArrES arg \<equiv> 
      let ((lst,len),(idx,chf,inp)) = arg;
          i = (if unat idx < unat len then (unat idx) else 0);
          elm = nth lst i; chres = chf(elm, inp)
      in ((list_update lst i (fst chres),len), snd chres)"

definition modrefArrES :: "'el CArrES\<^sub>T \<times> ('idx::len word \<times> ('pel \<times> 'arg \<Rightarrow> 'pel \<times> 'out) \<times> 'arg) \<Rightarrow> 'el CArrES\<^sub>T \<times> 'out"
  where
    "modrefArrES arg \<equiv> 
      let ((lst,len),(idx,chf,inp)) = arg;
          i = (if unat idx < unat len then (unat idx) else 0);
          elm = nth lst i; chres = chf(toPtr elm, inp)
      in ((list_update lst i (frPtr (fst chres)),len), snd chres)"

adhoc_overloading getArr getArrES
  and setArr setArrES
  and modifyArr modifyArrES
  and modrefArr modrefArrES

end
