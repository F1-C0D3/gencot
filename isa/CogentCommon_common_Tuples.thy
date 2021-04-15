theory CogentCommon_common_Tuples
  imports "ShallowShared_Tuples"
begin

text \<open>Iteration Functions\<close>

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

text \<open>seq32_simple\<close>

text \<open>As basic implementation we use a recursive function which counts from 0 in steps of 1.\<close>
fun seq32_simple_imp :: "nat \<Rightarrow> ('acc \<Rightarrow> 'acc) \<Rightarrow> 'acc \<Rightarrow> 'acc" where
    "seq32_simple_imp 0 f acc = acc" |
    "seq32_simple_imp (Suc n) f acc = f (seq32_simple_imp n f acc)"

text \<open>Function seq32_simple is defined by reduction to seq32_simple_imp.\<close>
axiomatization where seq32_simple_def: 
  "\<And>(acc::'acc) (f::'acc \<Rightarrow> 'acc). seq32_term to step \<Longrightarrow> 
     seq32_simple \<lparr>Seq32SimpleParam.frm\<^sub>f=frm, to\<^sub>f=to, step\<^sub>f=step, f\<^sub>f=f, acc\<^sub>f=acc\<rparr> \<equiv> 
       seq32_simple_imp (seq32_cnt frm to step) f acc"

text \<open>Induction rules for seq32_simple:\<close>

text \<open>The first induction rule is intended for properties P which do not depend on the current loop counter,
      i.e., true loop invariants. For the induction step it must be proven than an every application of function
      f preserves P.\<close>
lemma seq32_simple_imp_induct_f: "(P acc) \<Longrightarrow> (\<And>a. (P a) \<Longrightarrow> (P (f a))) \<Longrightarrow> (P (seq32_simple_imp n f acc))"
  by (induct n, auto)

lemma seq32_simple_induct_f:
  "seq32_term to step \<Longrightarrow> P(acc) \<Longrightarrow> (\<And>a. P(a) \<Longrightarrow> P(f(a))) \<Longrightarrow>
   P(seq32_simple \<lparr>Seq32SimpleParam.frm\<^sub>f=frm, to\<^sub>f=to, step\<^sub>f=step, f\<^sub>f=f, acc\<^sub>f=acc \<rparr>)"
  by(unfold seq32_simple_def, rule seq32_simple_imp_induct_f, auto)

text \<open>The second induction rule is intended for properties P which additionally depend on the current loop counter.
      For the induction step it must be proven that every application of function f preserves P for the incremented
      loop counter. As additional induction premise the loop counter can be assumed to be lower than the overall
      number of iterations in the final thesis.\<close>
lemma seq32_simple_imp_induct: "(P 0 acc) \<Longrightarrow> (\<And>a i. i < n \<Longrightarrow> (P i a) \<Longrightarrow> (P (Suc i) (f a))) \<Longrightarrow> (P n (seq32_simple_imp n f acc))"
  by (induct n, auto)

lemma seq32_simple_induct:
  "seq32_term to step \<Longrightarrow> (P 0 acc) \<Longrightarrow> (\<And>a i. i < (seq32_cnt frm to step) \<Longrightarrow> (P i a) \<Longrightarrow> (P (Suc i) (f a))) \<Longrightarrow>
   (P (seq32_cnt frm to step) (seq32_simple \<lparr>Seq32SimpleParam.frm\<^sub>f=frm, to\<^sub>f=to, step\<^sub>f=step, f\<^sub>f=f, acc\<^sub>f=acc \<rparr>))"
  by (unfold seq32_simple_def, rule seq32_simple_imp_induct, auto)

text \<open>seq32\<close>

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

text \<open>The induction rule is intended for properties P which additionally depend on the current loop counter and the observed term.
      The induction step consists of two parts for the cases Iterate and Break.
      For the first case it must be proven that every application of function f preserves P for the incremented
      loop counter. For the second case it must be proven that P holds for the incremented loop counter.
      As additional induction premise the loop counter can be assumed to be lower than the overall
      number of iterations in the final thesis.\<close>

lemma seq32_imp_induct:
  "P 0 (acc, Iterate()) obsv \<Longrightarrow> 
   (\<And>a i r. i < n \<Longrightarrow> 
      (P i (a,Iterate()) obsv \<longrightarrow> 
           P (Suc i) (f \<lparr>Seq32_bodyParam.acc\<^sub>f=a, obsv\<^sub>f=obsv, idx\<^sub>f=frm+(of_nat i)*step\<rparr>) obsv)
    \<and> (P i (a,Break r) obsv \<longrightarrow> P (Suc i) (a,Break r) obsv)) \<Longrightarrow> 
   P n (seq32_imp n f acc frm step obsv) obsv"
  apply(induct n)
   apply(simp add:split_def)
  apply(case_tac "seq32_imp n f acc frm step obsv")
  apply(case_tac b)
  by auto

lemma seq32_induct:   
  "seq32_term to step \<Longrightarrow> 
   P 0 (acc,Iterate()) obsv \<Longrightarrow> 
   (\<And>a i r. i < (seq32_cnt frm to step) \<Longrightarrow> 
       (P i (a,Iterate()) obsv \<longrightarrow>
           P (Suc i) (f \<lparr>Seq32_bodyParam.acc\<^sub>f=a, obsv\<^sub>f = obsv, idx\<^sub>f=frm+(of_nat i)*step \<rparr>) obsv)
     \<and> (P i (a,Break r) obsv \<longrightarrow> P (Suc i) (a,Break r) obsv)) \<Longrightarrow>
   P (seq32_cnt frm to step) (seq32 \<lparr>Seq32Param.frm\<^sub>f=frm, to\<^sub>f=to, step\<^sub>f=step, f\<^sub>f=f, acc\<^sub>f=acc, obsv\<^sub>f = obsv \<rparr>) obsv"
  for f::"('acc, 'obsv, 'rbrk) Seq32_body" and acc::'acc and obsv::'obsv
  apply(unfold seq32_def)
  apply(rule_tac P=P  in seq32_imp_induct)
  by auto

end
