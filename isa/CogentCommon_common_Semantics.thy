theory CogentCommon_common_Semantics
  imports "CogentCommon_common_Tuples"
begin

text \<open>Induction rules for seq32_simple:\<close>

text \<open>The first induction rule is intended for properties P which do not depend on the current loop counter,
      i.e., true loop invariants. For the induction step it must be proved than every application of function
      f preserves P.\<close>
lemma seq32_simple_imp_induct_f: "(P acc) \<Longrightarrow> (\<And>a. (P a) \<Longrightarrow> (P (f a))) \<Longrightarrow> (P (seq32_simple_imp n f acc))"
  by (induct n, auto)

lemma seq32_simple_induct_f:
  "seq32_term to step \<Longrightarrow> P(acc) \<Longrightarrow> (\<And>a. P(a) \<Longrightarrow> P(f(a))) \<Longrightarrow>
   P(seq32_simple \<lparr>Seq32SimpleParam.frm\<^sub>f=frm, to\<^sub>f=to, step\<^sub>f=step, f\<^sub>f=f, acc\<^sub>f=acc \<rparr>)"
  by(unfold seq32_simple_def, rule seq32_simple_imp_induct_f, auto)

text \<open>The second induction rule is intended for properties P which additionally depend on the current loop counter.
      For the induction step it must be proved that every application of function f preserves P for the incremented
      loop counter. As additional induction premise the loop counter can be assumed to be lower than the overall
      number of iterations in the final thesis.\<close>
lemma seq32_simple_imp_induct: "(P 0 acc) \<Longrightarrow> (\<And>a i. i < n \<Longrightarrow> (P i a) \<Longrightarrow> (P (Suc i) (f a))) \<Longrightarrow> (P n (seq32_simple_imp n f acc))"
  by (induct n, auto)

lemma seq32_simple_induct_P:
  "seq32_term to step \<Longrightarrow> 
   (P 0 acc) \<Longrightarrow> 
   (\<And>a i. i < (seq32_cnt frm to step) \<Longrightarrow> (P i a) \<Longrightarrow> (P (Suc i) (f a))) \<Longrightarrow>
   (P (seq32_cnt frm to step) (seq32_simple \<lparr>Seq32SimpleParam.frm\<^sub>f=frm, to\<^sub>f=to, step\<^sub>f=step, f\<^sub>f=f, acc\<^sub>f=acc \<rparr>))"
  by (unfold seq32_simple_def, rule seq32_simple_imp_induct, auto)

text \<open>The following rule can be used in the special case where the invariant specifies a function
\<open>sf\<close> for the current body result, which depends on the current number of iterations and the initial 
accumulator.\<close>

lemma seq32_simple_induct_eq:
  "seq32_term to step \<Longrightarrow> 
   cnt = seq32_cnt frm to step \<Longrightarrow>
   acc = sf 0 acc \<Longrightarrow> 
   (\<And>a i. i < cnt \<Longrightarrow> a = (sf i acc) \<Longrightarrow> (f a) = (sf (Suc i) acc)) \<Longrightarrow>
   seq32_simple \<lparr>Seq32SimpleParam.frm\<^sub>f=frm, to\<^sub>f=to, step\<^sub>f=step, f\<^sub>f=f, acc\<^sub>f=acc \<rparr> = sf cnt acc"
  apply(simp)
  apply(rule seq32_simple_induct_P[where P="\<lambda>cnt a. a = sf cnt acc"])
  by(simp_all)

text \<open>The following rules can be used when the loop starts at \<open>0\<close> and counts in steps of \<open>1\<close>. In this
case it always terminates and the assumptions are only the induction start and step.\<close>

lemma seq32_cnt_01: "seq32_cnt 0 to 1 = unat to"
  by(simp add: seq32_cnt_def)

lemma seq32_simple_induct_P_01:
  "(P 0 acc) \<Longrightarrow> 
   (\<And>a i. i < (unat cnt) \<Longrightarrow> (P i a) \<Longrightarrow> (P (Suc i) (f a))) \<Longrightarrow>
   (P (unat cnt) (seq32_simple \<lparr>Seq32SimpleParam.frm\<^sub>f=0, to\<^sub>f=cnt, step\<^sub>f=1, f\<^sub>f=f, acc\<^sub>f=acc \<rparr>))"
  apply(subst seq32_cnt_01[symmetric])
  apply (rule seq32_simple_induct_P)
  by(auto simp add: seq32_term_def seq32_cnt_01,unat_arith,auto)

lemma seq32_simple_induct_eq_01:
  "acc = sf 0 acc \<Longrightarrow> 
   (\<And>a i. i < (unat cnt) \<Longrightarrow> a = (sf i acc) \<Longrightarrow> (f a) = (sf (Suc i) acc)) \<Longrightarrow>
   seq32_simple \<lparr>Seq32SimpleParam.frm\<^sub>f=0, to\<^sub>f=cnt, step\<^sub>f=1, f\<^sub>f=f, acc\<^sub>f=acc \<rparr> = sf (unat cnt) acc"
  apply(rule seq32_simple_induct_eq)
  by(auto simp add: seq32_term_def seq32_cnt_def,unat_arith,auto)

text \<open>Induction rules for seq32:\<close>

text \<open>Here the induction step consists of two parts for the cases Iterate and Break.
      For the first case it must be proven that every application of function f preserves the invariant 
      for the incremented loop counter. For the second case it must be proven that the invariant also 
      holds for the incremented loop counter without applying f.\<close>

lemma seq32_imp_induct:
  "P 0 (acc, Iterate()) acc obsv \<Longrightarrow> 
   (\<And>a i r. i < n \<Longrightarrow> 
      (P i (a,Iterate()) acc obsv \<longrightarrow> 
           P (Suc i) (f \<lparr>Seq32_bodyParam.acc\<^sub>f=a, obsv\<^sub>f=obsv, idx\<^sub>f=frm+(of_nat i)*step\<rparr>) acc obsv)
    \<and> (P i (a,Break r) acc obsv \<longrightarrow> P (Suc i) (a,Break r) acc obsv)) \<Longrightarrow> 
   P n (seq32_imp n f acc frm step obsv) acc obsv"
  apply(induct n)
   apply(simp add:split_def)
  apply(case_tac "seq32_imp n f acc frm step obsv")
  apply(case_tac b)
  by auto

text \<open>The most general form of the rule can be applied to an arbitrary invariant \<open>P\<close> which depends
on the initial accumulator and observed value and on the current number of iterations and the current
body result.\<close>

lemma seq32_induct_P:   
  "seq32_term to step \<Longrightarrow> 
   P 0 (acc,Iterate()) acc obsv \<Longrightarrow> 
   (\<And>a i r. i < (seq32_cnt frm to step) \<Longrightarrow> 
       (P i (a,Iterate()) acc obsv \<longrightarrow>
           P (Suc i) (f \<lparr>Seq32_bodyParam.acc\<^sub>f=a, obsv\<^sub>f = obsv, idx\<^sub>f=frm+(of_nat i)*step \<rparr>) acc obsv)
     \<and> (P i (a,Break r) acc obsv \<longrightarrow> P (Suc i) (a,Break r) acc obsv)) \<Longrightarrow>
   P (seq32_cnt frm to step) (seq32 \<lparr>Seq32Param.frm\<^sub>f=frm, to\<^sub>f=to, step\<^sub>f=step, f\<^sub>f=f, acc\<^sub>f=acc, obsv\<^sub>f = obsv \<rparr>) acc obsv"
  for f::"('acc, 'obsv, 'rbrk) Seq32_body" and acc::'acc and obsv::'obsv
  apply(unfold seq32_def)
  apply(rule_tac P=P  in seq32_imp_induct)
  by auto

text \<open>The following rule can be used in the special case where the invariant specifies a function
\<open>sf\<close> for the current body result, which depends on the current number of iterations and the initial 
accumulator and observed value.\<close>

lemma seq32_induct_eq: 
   "seq32_term to step \<Longrightarrow>
    cnt =  seq32_cnt frm to step \<Longrightarrow>
   (acc,Iterate()) = sf 0 acc obsv \<Longrightarrow> 
   (\<And>a i r. i < cnt \<Longrightarrow> 
       ((a,Iterate()) = sf i acc obsv \<longrightarrow>
           f \<lparr>Seq32_bodyParam.acc\<^sub>f=a, obsv\<^sub>f = obsv, idx\<^sub>f=frm+(of_nat i)*step \<rparr> = sf (Suc i) acc obsv)
     \<and> ((a,Break r) = sf i acc obsv \<longrightarrow> (a,Break r) = sf (Suc i) acc obsv)) \<Longrightarrow>
   seq32 \<lparr>Seq32Param.frm\<^sub>f=frm, to\<^sub>f=to, step\<^sub>f=step, f\<^sub>f=f, acc\<^sub>f=acc, obsv\<^sub>f = obsv \<rparr> = sf cnt acc obsv"
   for f::"('acc, 'obsv, 'rbrk) Seq32_body" and acc::'acc and obsv::'obsv
  apply(simp)
  apply(rule seq32_induct_P[where P="\<lambda>cnt lrr acc obsv. lrr = sf cnt acc obsv"])
  by(simp_all)

text \<open>The following rule can be used when the loop starts at \<open>0\<close> and counts in steps of \<open>1\<close>. In this
case it always terminates and the assumptions are only the induction start and step.\<close>

lemma seq32_induct_P_01:
  "P 0 (acc,Iterate()) acc obsv \<Longrightarrow> 
   (\<And>a i r. i < (unat to) \<Longrightarrow> 
       (P i (a,Iterate()) acc obsv \<longrightarrow>
           P (Suc i) (f \<lparr>Seq32_bodyParam.acc\<^sub>f=a, obsv\<^sub>f = obsv, idx\<^sub>f=(of_nat i) \<rparr>) acc obsv)
     \<and> (P i (a,Break r) acc obsv \<longrightarrow> P (Suc i) (a,Break r) acc obsv)) \<Longrightarrow>
   P (unat to) (seq32 \<lparr>Seq32Param.frm\<^sub>f=0, to\<^sub>f=to, step\<^sub>f=1, f\<^sub>f=f, acc\<^sub>f=acc, obsv\<^sub>f = obsv \<rparr>) acc obsv"
  for f::"('acc, 'obsv, 'rbrk) Seq32_body" and acc::'acc and obsv::'obsv
  apply(subst seq32_cnt_01[symmetric])
  apply (rule seq32_induct_P[where P=P])
    by(simp_all add: seq32_term_def seq32_cnt_def, unat_arith,clarsimp)

lemma seq32_induct_eq_01: 
  "(acc,Iterate()) = sf 0 acc obsv \<Longrightarrow> 
   (\<And>a i r. i < (unat cnt) \<Longrightarrow> 
       ((a,Iterate()) = sf i acc obsv \<longrightarrow>
           f \<lparr>Seq32_bodyParam.acc\<^sub>f=a, obsv\<^sub>f = obsv, idx\<^sub>f=(of_nat i) \<rparr> = sf (Suc i) acc obsv)
     \<and> ((a,Break r) = sf i acc obsv \<longrightarrow> (a,Break r) = sf (Suc i) acc obsv)) \<Longrightarrow>
   seq32 \<lparr>Seq32Param.frm\<^sub>f=0, to\<^sub>f=cnt, step\<^sub>f=1, f\<^sub>f=f, acc\<^sub>f=acc, obsv\<^sub>f = obsv \<rparr> = sf (unat cnt) acc obsv"
   for f::"('acc, 'obsv, 'rbrk) Seq32_body" and acc::'acc and obsv::'obsv
  apply(rule seq32_induct_eq)
  by(auto simp add: seq32_term_def seq32_cnt_def,unat_arith,auto)

text \<open>Induction rule for seq64:\<close>

text \<open>Analogous to seq32.\<close>

lemma seq64_imp_induct:
  "P 0 (acc, Iterate()) obsv \<Longrightarrow> 
   (\<And>a i r. i < n \<Longrightarrow> 
      (P i (a,Iterate()) obsv \<longrightarrow> 
           P (Suc i) (f \<lparr>Seq32_bodyParam.acc\<^sub>f=a, obsv\<^sub>f=obsv, idx\<^sub>f=frm+(of_nat i)*step\<rparr>) obsv)
    \<and> (P i (a,Break r) obsv \<longrightarrow> P (Suc i) (a,Break r) obsv)) \<Longrightarrow> 
   P n (seq64_imp n f acc frm step obsv) obsv"
  apply(induct n)
   apply(simp add:split_def)
  apply(case_tac "seq64_imp n f acc frm step obsv")
  apply(case_tac b)
  by auto

lemma seq64_induct:   
  "seq64_term to step \<Longrightarrow> 
   P 0 (acc,Iterate()) obsv \<Longrightarrow> 
   (\<And>a i r. i < (seq64_cnt frm to step) \<Longrightarrow> 
       (P i (a,Iterate()) obsv \<longrightarrow>
           P (Suc i) (f \<lparr>Seq32_bodyParam.acc\<^sub>f=a, obsv\<^sub>f = obsv, idx\<^sub>f=frm+(of_nat i)*step \<rparr>) obsv)
     \<and> (P i (a,Break r) obsv \<longrightarrow> P (Suc i) (a,Break r) obsv)) \<Longrightarrow>
   P (seq64_cnt frm to step) (seq64 \<lparr>Seq32Param.frm\<^sub>f=frm, to\<^sub>f=to, step\<^sub>f=step, f\<^sub>f=f, acc\<^sub>f=acc, obsv\<^sub>f = obsv \<rparr>) obsv"
  for f::"('acc, 'obsv, 'rbrk) Seq64_body" and acc::'acc and obsv::'obsv
  apply(unfold seq64_def)
  apply(rule_tac P=P  in seq64_imp_induct)
  by auto

end