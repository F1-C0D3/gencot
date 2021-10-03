theory Gencot_ESArray_Tuples
  imports ShallowShared_Tuples
    Gencot_CArray_Tuples
    "HOL-Library.Adhoc_Overloading"
begin

text \<open>Define the array functions for explicitly sized arrays\<close>

definition getArrES :: "'el CArrES\<^sub>T \<times> 'idx::len word \<Rightarrow> 'el"
  where 
    "getArrES arg \<equiv>
      let ((lst,len),idx) = arg
      in if unat idx >= unat len then hd lst
         else (nth lst (unat idx))"

definition setArrES :: "'el CArrES\<^sub>T \<times> 'idx::len word \<times> 'el \<Rightarrow> 'el CArrES\<^sub>T"
  where
    "setArrES arg \<equiv> 
      let ((lst,len),idx,elm) = arg
      in if unat idx >= unat len then (lst,len)
         else ((list_update lst (unat idx) elm),len)"

definition modifyArrES :: "'el CArrES\<^sub>T \<times> 'idx::len word \<times> ('el \<times> 'arg \<Rightarrow> 'el \<times> 'arg) \<times> 'arg \<Rightarrow> 'el CArrES\<^sub>T \<times> 'arg"
  where
    "modifyArrES arg \<equiv> 
      let ((lst,len),idx,chf,inp) = arg
      in if unat idx >= unat len then ((lst,len), inp)
         else let elm = nth lst (unat idx); chres = chf(elm, inp)
           in ((list_update lst (unat idx) (fst chres),len), snd chres)"

definition modifyArrDfltES :: "'el CArrES\<^sub>T \<times> 'idx::len word \<times> ('el \<times> 'arg \<Rightarrow> 'el \<times> 'out) \<times> 'arg \<Rightarrow> 'el CArrES\<^sub>T \<times> 'out"
  where
    "modifyArrDfltES arg \<equiv> 
      let ((lst,len),idx,chf,inp) = arg
      in if unat idx >= unat len then ((lst,len), defaultVal ())
         else let elm = nth lst (unat idx); chres = chf(elm, inp)
           in ((list_update lst (unat idx) (fst chres),len), snd chres)"

definition modrefArrES :: "'el CArrES\<^sub>T \<times> 'idx::len word \<times> ('pel \<times> 'arg \<Rightarrow> 'pel \<times> 'arg) \<times> 'arg \<Rightarrow> 'el CArrES\<^sub>T \<times> 'arg"
  where
    "modrefArrES arg \<equiv> 
      let ((lst,len),idx,chf,inp) = arg
      in if unat idx >= unat len then ((lst,len), inp)
         else let elm = nth lst (unat idx); chres = chf(toPtr elm, inp)
           in ((list_update lst (unat idx) (frPtr (fst chres)),len), snd chres)"

definition modrefArrDfltES :: "'el CArrES\<^sub>T \<times> 'idx::len word \<times> ('pel \<times> 'arg \<Rightarrow> 'pel \<times> 'out) \<times> 'arg \<Rightarrow> 'el CArrES\<^sub>T \<times> 'out"
  where
    "modrefArrDfltES arg \<equiv> 
      let ((lst,len),idx,chf,inp) = arg
      in if unat idx >= unat len then ((lst,len), defaultVal ())
         else let elm = nth lst (unat idx); chres = chf(toPtr elm, inp)
           in ((list_update lst (unat idx) (frPtr (fst chres)),len), snd chres)"

adhoc_overloading getArr getArrES
  and setArr setArrES
  and modifyArr modifyArrES
  and modifyArrDflt modifyArrDfltES
  and modrefArr modrefArrES
  and modrefArrDflt modrefArrDfltES

end
