theory CogentCommon_common
  imports ShallowShared
begin

fun seq32_simple_imp :: "nat \<Rightarrow> ('acc \<Rightarrow> 'acc) \<Rightarrow> 'acc \<Rightarrow> 'acc" where
    "seq32_simple_imp cnt f acc = 
      (if cnt = 0 then acc 
       else seq32_simple_imp (cnt-1) f (f acc))"

axiomatization where seq32_simple_def[simp]: 
  "\<And>(acc::'acc) (f::'acc \<Rightarrow> 'acc). step \<noteq> 0 \<Longrightarrow> seq32_simple (Seq32SimpleParam.make frm to step f acc) = seq32_simple_imp (unat ((to - frm + step) div step)) f acc"

thm seq32_simple_imp.simps

fun seq32_imp :: "nat \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> ('acc, 'obsv, 'rbrk) Seq32_body \<Rightarrow> 'acc \<Rightarrow> 'obsv \<Rightarrow> ('acc, 'rbrk) LRR\<^sub>T" where
  "seq32_imp cnt idx step f acc obsv = 
    (if cnt = 0 then RR.make acc (Iterate ())
     else let fres = f (Seq32_bodyParam.make acc obsv idx) 
          in case RR.p2\<^sub>f fres of Break _ \<Rightarrow> fres
             | Iterate() \<Rightarrow> seq32_imp (cnt-1) (idx+step) step f (RR.p1\<^sub>f fres) obsv)"

axiomatization where seq32_step0[simp]: 
  "\<And>(acc::'acc) (obsv::'obsv) (f::('acc, 'obsv, 'rbrk) Seq32_body) .seq32 (Seq32Param.make frm to 0 f acc obsv) = RR.make acc (Iterate())"
axiomatization where seq32_def[simp]: 
  "\<And>(acc::'acc) (obsv::'obsv) (f::('acc, 'obsv, 'rbrk) Seq32_body) .step \<noteq> 0 \<Longrightarrow> seq32 (Seq32Param.make frm to step f acc obsv) = seq32_imp (unat ((to - frm + step) div step)) frm step f acc obsv"

end
