theory CogentCommon_common
  imports ShallowShared
begin

section \<open>Iteration Functions\<close>

text \<open>
Non-tuples form. For detailed description see theory \<open>CogentCommon_common_Tuples\<close>.
\<close>

subsection \<open>32 Bit Functions\<close>

definition seq32_cnt :: "32 word \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> nat" where
  "seq32_cnt frm to step \<equiv> ((unat to)-(unat frm)+(unat step)-1) div (unat step)"

definition seq32_term :: "32 word \<Rightarrow> 32 word \<Rightarrow> bool" where 
  "seq32_term to step \<equiv> (step > 0) \<and> ((unat to) + (unat step) \<le> 2 ^ LENGTH(32))"

subsubsection \<open>seq32_simple\<close>

fun seq32_simple_imp :: "nat \<Rightarrow> ('acc \<Rightarrow> 'acc) \<Rightarrow> 'acc \<Rightarrow> 'acc" where
    "seq32_simple_imp 0 f acc = acc" |
    "seq32_simple_imp (Suc n) f acc = f (seq32_simple_imp n f acc)"

axiomatization where seq32_simple_def: 
  "\<And>(acc::'acc) (f::'acc \<Rightarrow> 'acc). seq32_term to step \<Longrightarrow> 
     seq32_simple \<lparr>Seq32SimpleParam.frm\<^sub>f=frm, to\<^sub>f=to, step\<^sub>f=step, f\<^sub>f=f, acc\<^sub>f=acc\<rparr> \<equiv> 
       seq32_simple_imp (seq32_cnt frm to step) f acc"

subsubsection \<open>seq32\<close>

fun seq32_imp :: "nat \<Rightarrow> ('acc, 'obsv, 'rbrk) Seq32_body \<Rightarrow> 'acc \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> 'obsv \<Rightarrow> ('acc, 'rbrk) LRR\<^sub>T" where
    "seq32_imp 0 f acc frm step obsv = makeTup2 acc (Iterate())" |
    "seq32_imp (Suc n) f acc frm step obsv = 
       (let x = seq32_imp n f acc frm step obsv
        in case p2Tup2 x of
          Break _ \<Rightarrow> x |
          Iterate _ \<Rightarrow> f \<lparr>Seq32_bodyParam.acc\<^sub>f = p1Tup2 x, obsv\<^sub>f = obsv, idx\<^sub>f = frm + (of_nat n)*step \<rparr>)"

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
    "seq64_imp 0 f acc frm step obsv = makeTup2 acc (Iterate())" |
    "seq64_imp (Suc n) f acc frm step obsv = 
       (let x = seq64_imp n f acc frm step obsv
        in case p2Tup2 x of
          Break _ \<Rightarrow> x |
          Iterate _ \<Rightarrow> f \<lparr>Seq32_bodyParam.acc\<^sub>f = p1Tup2 x, obsv\<^sub>f = obsv, idx\<^sub>f = frm + (of_nat n)*step \<rparr>)"

axiomatization where seq64_def: 
  "\<And>(acc::'acc) (obsv::'obsv) (f::('acc, 'obsv, 'rbrk) Seq64_body). seq64_term to step \<Longrightarrow> 
     seq64 \<lparr>Seq32Param.frm\<^sub>f=frm, to\<^sub>f=to, step\<^sub>f=step, f\<^sub>f=f, acc\<^sub>f=acc, obsv\<^sub>f=obsv\<rparr> \<equiv> 
       seq64_imp (seq64_cnt frm to step) f acc frm step obsv"

end
