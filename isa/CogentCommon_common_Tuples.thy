theory CogentCommon_common_Tuples
  imports "ShallowShared_Tuples"
begin

section \<open>Iteration Functions\<close>

subsection \<open>32 Bit Functions\<close>

text \<open>Auxiliary functions:
      seq32_cnt is used to calculate the number of intended iterations from start, end and step values. 
      seq32_term is used as premise for termination. 
        Even if the end value is specified, due to word arithmetic the loop counter could overflow in the
        last step and start again. (This can only happen if the step is not 1). 
        We use a simplified condition here, which is slightly stronger than necessary.
        Another reason for non-termination would be if step is 0 (which is not tested in the C implementation
        of seq32_simple).\<close>

definition seq32_cnt :: "32 word \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> nat" where
  "seq32_cnt frm to step \<equiv> ((unat to)-(unat frm)+(unat step)-1) div (unat step)"

definition seq32_term :: "32 word \<Rightarrow> 32 word \<Rightarrow> bool" where 
  "seq32_term to step \<equiv> (step > 0) \<and> ((unat to) + (unat step) \<le> 2 ^ LENGTH(32))"

subsubsection \<open>seq32_simple\<close>

text \<open>As basic implementation we use a recursive function which counts from 0 in steps of 1.\<close>
fun seq32_simple_imp :: "nat \<Rightarrow> ('acc \<Rightarrow> 'acc) \<Rightarrow> 'acc \<Rightarrow> 'acc" where
    "seq32_simple_imp 0 f acc = acc" |
    "seq32_simple_imp (Suc n) f acc = f (seq32_simple_imp n f acc)"

text \<open>Function seq32_simple is defined by reduction to seq32_simple_imp.\<close>
axiomatization where seq32_simple_def: 
  "\<And>(acc::'acc) (f::'acc \<Rightarrow> 'acc). seq32_term to step \<Longrightarrow> 
     seq32_simple \<lparr>Seq32SimpleParam.frm\<^sub>f=frm, to\<^sub>f=to, step\<^sub>f=step, f\<^sub>f=f, acc\<^sub>f=acc\<rparr> \<equiv> 
       seq32_simple_imp (seq32_cnt frm to step) f acc"

subsubsection \<open>seq32\<close>

text \<open>As basic implementation we use a recursive function which counts from 0 in steps of 1.
      It takes the start, step, and obsv values as additional arguments for providing the arguments of the body function.\<close>
fun seq32_imp :: "nat \<Rightarrow> ('acc, 'obsv, 'rbrk) Seq32_body \<Rightarrow> 'acc \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> 'obsv \<Rightarrow> ('acc, 'rbrk) LRR\<^sub>T" where
    "seq32_imp 0 f acc frm step obsv = (acc, Iterate())" |
    "seq32_imp (Suc n) f acc frm step obsv = 
       (let (acc, lres) = seq32_imp n f acc frm step obsv
        in case lres of
          Break _ \<Rightarrow> (acc, lres) |
          Iterate _ \<Rightarrow> f \<lparr>Seq32_bodyParam.acc\<^sub>f = acc, obsv\<^sub>f = obsv, idx\<^sub>f = frm + (of_nat n)*step \<rparr>)"

text \<open>Function seq32 is defined by reduction to seq32_imp.\<close>
axiomatization where seq32_def: 
  "\<And>(acc::'acc) (obsv::'obsv) (f::('acc, 'obsv, 'rbrk) Seq32_body). seq32_term to step \<Longrightarrow> 
     seq32 \<lparr>Seq32Param.frm\<^sub>f=frm, to\<^sub>f=to, step\<^sub>f=step, f\<^sub>f=f, acc\<^sub>f=acc, obsv\<^sub>f=obsv\<rparr> \<equiv> 
       seq32_imp (seq32_cnt frm to step) f acc frm step obsv"

subsection \<open>64 Bit Functions\<close>

text \<open>Analogous to 32 bit functions.\<close>

definition seq64_cnt :: "64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> nat" where
  "seq64_cnt frm to step \<equiv> ((unat to)-(unat frm)+(unat step)-1) div (unat step)"

definition seq64_term :: "64 word \<Rightarrow> 64 word \<Rightarrow> bool" where 
  "seq64_term to step \<equiv> (step > 0) \<and> ((unat to) + (unat step) \<le> 2 ^ LENGTH(64))"

subsubsection \<open>seq64\<close>

fun seq64_imp :: "nat \<Rightarrow> ('acc, 'obsv, 'rbrk) Seq64_body \<Rightarrow> 'acc \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> 'obsv \<Rightarrow> ('acc, 'rbrk) LRR\<^sub>T" where
    "seq64_imp 0 f acc frm step obsv = (acc, Iterate())" |
    "seq64_imp (Suc n) f acc frm step obsv = 
       (let (acc, lres) = seq64_imp n f acc frm step obsv
        in case lres of
          Break _ \<Rightarrow> (acc, lres) |
          Iterate _ \<Rightarrow> f \<lparr>Seq32_bodyParam.acc\<^sub>f = acc, obsv\<^sub>f = obsv, idx\<^sub>f = frm + (of_nat n)*step \<rparr>)"

axiomatization where seq64_def: 
  "\<And>(acc::'acc) (obsv::'obsv) (f::('acc, 'obsv, 'rbrk) Seq64_body). seq64_term to step \<Longrightarrow> 
     seq64 \<lparr>Seq32Param.frm\<^sub>f=frm, to\<^sub>f=to, step\<^sub>f=step, f\<^sub>f=f, acc\<^sub>f=acc, obsv\<^sub>f=obsv\<rparr> \<equiv> 
       seq64_imp (seq64_cnt frm to step) f acc frm step obsv"

end
