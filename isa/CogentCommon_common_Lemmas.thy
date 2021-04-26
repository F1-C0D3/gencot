theory CogentCommon_common_Lemmas
  imports "CogentCommon_common_Tuples"
begin

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

text \<open>Induction rule for seq32:\<close>

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