theory Gencot_MapSupport
  imports Main
begin

section \<open>Map Support Extensions\<close>

text \<open>
This is an extension of \<^theory>\<open>HOL.Map\<close> intended as basis for reasoning support for Gencot arrays.
Note that there are also theories \<^theory_text>\<open>HOL-Library.Finite_Map\<close> and \<^theory_text>\<open>HOL-Library.Mapping\<close>.
Some properties here may be replicated from them, but they introduce subtypes with no support for 
the map type syntax \<open>A \<rightharpoonup> B\<close>.
\<close>

subsection \<open>Additional Theorems for Maps\<close>

lemma map_comp_restrict_ran:
 "ran m1 \<subseteq> A \<Longrightarrow> m2 \<circ>\<^sub>m m1 = (m2 |` A) \<circ>\<^sub>m m1"
  apply(rule ext)
  apply(simp add: map_comp_def)
  apply(case_tac "m1 x",simp)
  by(auto simp add: restrict_map_def ran_def)

lemma map_comp_restrict_ran':
 "ran m1 \<subseteq> dom m2 \<Longrightarrow> m2 \<subseteq>\<^sub>m m2' \<Longrightarrow> m2' \<circ>\<^sub>m m1 = m2 \<circ>\<^sub>m m1"
  apply(rule ext)
  apply(simp add: map_comp_def)
  apply(case_tac "m1 x",simp)
  apply(simp add: ran_def dom_def)
  by (smt Ball_Collect domI map_le_def mem_Collect_eq)

lemma restrict_dom_m_is_m: 
 "m1 \<subseteq>\<^sub>m m2 \<Longrightarrow> m2 |` (dom m1) = m1"
  by(auto simp add: restrict_map_def map_le_def dom_def)

lemma map_le_implies_ran_le: "(m \<subseteq>\<^sub>m m') \<Longrightarrow> (ran m \<subseteq> ran m')"
  apply(simp add: map_le_def ran_def)
  by (smt Collect_mono domIff option.simps(3))

lemma restrict_map_le:
 "m |`A \<subseteq>\<^sub>m m"
  by (simp add: map_le_def)

lemma dom_comp: 
 "ran m1 \<subseteq> dom m2 \<Longrightarrow> dom (m2 \<circ>\<^sub>m m1) = dom m1"
  apply(simp add: map_comp_def dom_def ran_def)
  apply(rule Collect_cong,rule iffI)
   apply(erule exE)
   apply(case_tac "m1 a",simp)
  by(auto)

lemma ran_comp:
 "ran (m2 \<circ>\<^sub>m m1) = ran (m2 |` (ran m1))"
  apply(auto simp add: map_comp_def ran_def restrict_map_def)
  apply (metis option.case_eq_if option.collapse option.distinct(1))
  by (metis option.simps(5))

lemma Some_comp:
 "Some \<circ>\<^sub>m Some = Some"
  by(simp add: map_comp_def)

subsection \<open>Splitting and Pairing Maps\<close>

definition times_option :: "('a option) \<Rightarrow> ('b option) \<Rightarrow> ('a \<times> 'b) option" (infixr "\<times>\<^sub>o" 80)
  where "x \<times>\<^sub>o y \<equiv> case x of None \<Rightarrow> None | Some x' \<Rightarrow> (case y of None \<Rightarrow> None | Some y' \<Rightarrow> Some (x',y'))"

definition map_scomp :: "('b \<Rightarrow> 'c \<rightharpoonup> 'd) \<Rightarrow> ('a \<rightharpoonup> 'b \<times> 'c) \<Rightarrow> ('a \<rightharpoonup> 'd)" (infixr "\<circ>\<^sub>m\<^sub>s" 80)
  where "m1 \<circ>\<^sub>m\<^sub>s m2 \<equiv> (case_prod m1) \<circ>\<^sub>m m2"

definition map_prod_map :: "('a \<rightharpoonup> 'b) \<Rightarrow> ('c \<rightharpoonup> 'd) \<Rightarrow> 'a \<Rightarrow> 'c \<rightharpoonup> ('b \<times> 'd)"
  where "map_prod_map m1 m2 \<equiv> \<lambda>x y. (m1 x) \<times>\<^sub>o (m2 y)"

definition dbl_arg :: "('a \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)"
  where "dbl_arg f \<equiv> \<lambda>x. f x x"

definition map_split_map :: "('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<rightharpoonup> 'd) \<Rightarrow> 'a \<rightharpoonup> ('b \<times> 'd)"
  where "map_split_map m1 m2 \<equiv> dbl_arg (map_prod_map m1 m2)"

definition prsvarg_map :: "('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<rightharpoonup> 'a \<times> 'b)"
  where "prsvarg_map m \<equiv> map_split_map Some m"

lemma prsvarg_map:
 "prsvarg_map m = (\<lambda>x. case m x of None \<Rightarrow> None | Some y \<Rightarrow> Some (x,y))"
  by(simp add: prsvarg_map_def map_split_map_def dbl_arg_def map_prod_map_def times_option_def)

lemma times_option_None_iff:
 "x \<times>\<^sub>o y = None \<longleftrightarrow> x = None \<or> y = None"
  by (simp add: times_option_def option.case_eq_if)

lemma times_option_Some_iff:
 "x \<times>\<^sub>o y = Some (x',y') \<longleftrightarrow> x = Some x' \<and> y = Some y'"
  apply (simp add: times_option_def)
  by (smt Pair_inject option.case_eq_if option.distinct(1) option.expand option.sel)

lemma map_scomp_None_iff:
 "(m1 \<circ>\<^sub>m\<^sub>s m2) x = None \<longleftrightarrow> (m2 x = None \<or> (\<exists>x' y'. m2 x = Some (x',y') \<and> m1 x' y' = None)) "
  by (simp add: map_scomp_def map_comp_None_iff)

lemma map_scomp_Some_iff:
 "(m1 \<circ>\<^sub>m\<^sub>s m2) x = Some v \<longleftrightarrow> (\<exists>x' y'. m2 x = Some (x',y') \<and> m1 x' y' = Some v)"
  by (simp add: map_scomp_def map_comp_Some_iff)

lemma map_prod_map_None_iff:
 "map_prod_map m1 m2 x y = None \<longleftrightarrow> m1 x = None \<or> m2 y = None"
  by(simp add: map_prod_map_def times_option_None_iff)

lemma map_prod_map_Some_iff:
 "map_prod_map m1 m2 x y = Some (x',y') \<longleftrightarrow> m1 x = Some x' \<and> m2 y = Some y'"
  by(simp add: map_prod_map_def times_option_Some_iff)

lemma map_split_map_None_iff:
 "map_split_map m1 m2 x = None \<longleftrightarrow> m1 x = None \<or> m2 x = None"
  by(simp add: map_split_map_def map_prod_map_None_iff dbl_arg_def)

lemma map_split_map_Some_iff:
 "map_split_map m1 m2 x = Some (x',y') \<longleftrightarrow> m1 x = Some x' \<and> m2 x = Some y'"
  by(simp add: map_split_map_def map_prod_map_Some_iff dbl_arg_def)

lemma prsvarg_map_None_iff:
 "prsvarg_map m x = None \<longleftrightarrow> m x = None"
  by(simp add: prsvarg_map_def map_split_map_None_iff)

lemma prsvarg_map_Some_iff:
 "prsvarg_map m x = Some (y,v) \<longleftrightarrow> (m x = Some v \<and> x = y)"
  by(auto simp add: prsvarg_map_def map_split_map_Some_iff)

lemma map_prod_map_comp:
 "map_prod_map (m1 \<circ>\<^sub>m m2) (m3 \<circ>\<^sub>m m4) x = (map_prod_map m1 m3) \<circ>\<^sub>m\<^sub>s (map_prod_map m2 m4 x)"
  apply(simp add: map_scomp_def map_prod_map_def map_comp_def)
  apply(case_tac "m2 x",simp add: times_option_None_iff[THEN iffD2])
  apply(rule ext,simp)
  apply(case_tac "m4 y",simp add: times_option_None_iff[THEN iffD2])
  by(simp add: times_option_Some_iff[THEN iffD2])

lemma map_split_map_comp:
 "map_split_map (m1 \<circ>\<^sub>m m2) (m3 \<circ>\<^sub>m m4) = (map_prod_map m1 m3) \<circ>\<^sub>m\<^sub>s (map_split_map m2 m4)"
  apply(simp add: map_split_map_def dbl_arg_def map_prod_map_comp)
  apply(rule ext)
  by (smt map_scomp_Some_iff option.collapse)

lemma prsvarg_map_comp:
 "(prsvarg_map (m1 \<circ>\<^sub>m m2)) = (map_prod_map Some m1) \<circ>\<^sub>m\<^sub>s (prsvarg_map m2)"
  apply(simp add: prsvarg_map_def)
  apply(subst Some_comp[symmetric])
  by(rule map_split_map_comp)

subsection \<open>Injectivity\<close>

definition inj_map :: "('a \<rightharpoonup> 'b) \<Rightarrow> bool"
  where "inj_map m \<equiv> inj_on m (dom m)"

lemma inj_map:
 "\<lbrakk>inj_map m; m x1 = Some y; m x2 = Some y\<rbrakk> \<Longrightarrow> x1 = x2"
  by(simp add: inj_map_def inj_on_def dom_def)

lemma inj_map_le:
 "m \<subseteq>\<^sub>m m' \<Longrightarrow> inj_map m' \<Longrightarrow> inj_map m"
  apply(simp add: inj_map_def map_le_def dom_def)
  by (smt inj_onI inj_on_eq_iff mem_Collect_eq)

lemma inj_map_restrict:
 "inj_map m \<Longrightarrow> inj_map (m |`A)"
  apply(rule_tac m'=m in inj_map_le)
  by(simp_all add: restrict_map_le)

lemma inj_map_comp:
 "inj_map m1 \<Longrightarrow> inj_map (m2 |`ran m1) \<Longrightarrow> inj_map (m2 \<circ>\<^sub>m m1)"
  apply(auto simp add: inj_map_def)
  apply(intro inj_onI)
  apply(simp add: restrict_map_def)
  apply(case_tac "m1 x",simp)
   apply(case_tac "m1 y",auto)
  apply(case_tac "m1 y",simp)
  apply(drule_tac x=a and y=aa in inj_onD)
     apply(auto simp add: ran_def)
  apply(drule_tac x=x and y=y in inj_onD)
  by(auto)

lemma inj_map_iff:
 "finite (dom m) \<Longrightarrow> inj_map m = (card (ran m) = card (dom m))"
  apply(simp add: inj_map_def inj_on_iff_eq_card)
  apply(rule arg_cong[where f="\<lambda>x. x=card (dom m)"])
  apply(subst (2) card_image[where f=Some,symmetric],simp)
  apply(rule arg_cong[where f="card"])
  by(auto simp add: ran_def dom_def image_def)

subsection \<open>Injective Part of a Map\<close>

definition inj_part :: "('a, 'b) map \<Rightarrow> ('a, 'b) map"
  where "inj_part m \<equiv> \<lambda>x. (if \<exists>! y \<in> (dom m). (m y) = (m x) then (m x) else None)"

definition inj_dom :: "('a, 'b) map \<Rightarrow> 'a set"
  where "inj_dom m = dom (inj_part m)"

definition inj_ran :: "('a, 'b) map \<Rightarrow> 'b set"
  where "inj_ran m = ran (inj_part m)"

lemma inj_part_inj:
 "inj_map (inj_part m)"
  apply(simp add: inj_part_def inj_map_def)
  apply(intro inj_onI)
   apply(subst (asm) dom_if)+
   apply(simp_all)
  by(blast)

lemma inj_map_is_inj_part:
 "inj_map m \<Longrightarrow> inj_part m = m"
  apply(simp add: inj_map_def inj_part_def)
  apply(rule ext)
  apply(case_tac "\<exists>!y. y \<in> dom m \<and> m y = m x")
   apply(simp_all)
  by (metis domIff inj_onD)

lemma inj_part_le:
 "inj_part m \<subseteq>\<^sub>m m"
  by(simp add: inj_part_def map_le_def dom_def)

lemma inj_dom: 
 "inj_dom m = {x \<in> dom m. \<exists>! y. m x = m y}"
  by(auto simp add: inj_dom_def inj_part_def dom_def)

lemma inj_dom_le:
 "dom (inj_part m) \<subseteq> dom m"
  by(simp add: inj_part_le map_le_implies_dom_le)

lemma inj_ran: 
 "inj_ran m = {x \<in> ran m. \<exists>! y. Some x = m y}"
  apply(simp add: inj_ran_def inj_part_def ran_def dom_def)
  apply(rule Collect_cong)
  apply(auto)
    apply(rule_tac x=y in exI,simp)
   by(metis,metis)

lemma inj_ran_le:
 "ran (inj_part m) \<subseteq> ran m"
  by(simp add: inj_part_le map_le_implies_ran_le)

lemma inj_part_None_iff:
 "inj_part m x = None \<longleftrightarrow> m x = None \<or> (\<exists> x' \<noteq> x. m x = m x')"
  apply(auto simp add: inj_part_def)
  apply(fastforce)
  by metis

lemma inj_part_Some_iff:
 "inj_part m x = Some y \<longleftrightarrow> m x = Some y \<and> (\<exists>! x. m x = Some y)"
  apply(auto simp add: inj_part_def)
  by(auto)

lemma inj_part_comp':
 "(inj_part m1) \<circ>\<^sub>m (inj_part m2) \<subseteq>\<^sub>m (inj_part (m1 \<circ>\<^sub>m m2))"
  apply(auto simp add: map_comp_Some_iff map_le_def)
  apply(simp add: inj_part_def)
  apply(rule conjI)
   apply (metis map_comp_simps(2) option.simps(3))
 by (smt domI is_none_code(2) is_none_simps(1) map_comp_Some_iff)

lemma inj_part_comp:
 "inj_map (m2 |` ran m1) \<Longrightarrow> inj_part (m2 \<circ>\<^sub>m m1) = m2 \<circ>\<^sub>m (inj_part m1)"
  apply(subst map_comp_restrict_ran[where A="ran m1"],simp)
  apply(subst map_comp_restrict_ran[where ?m2.0 =m2 and A="ran m1"])
   apply(simp add: inj_part_le map_le_implies_ran_le)
  apply(rule map_le_antisym)
  apply(simp add: map_le_def)
  apply(rule ballI)
  apply(simp add: inj_part_def inj_map_def dom_def map_comp_def)
  apply(intro conjI impI,simp)
   apply (metis option.case_eq_if option.collapse)
  apply(subst inj_map_is_inj_part[symmetric],simp)
  by(rule inj_part_comp')

subsection \<open>Inverse Maps\<close>

definition inverse_map :: "('a, 'b) map \<Rightarrow> ('b, 'a) map"
  where "inverse_map m \<equiv> 
     (Some \<circ> (the_inv_into (dom m) m) \<circ> Some) |` (ran m)"

definition inv_map :: "('a, 'b) map \<Rightarrow> ('b, 'a) map"
  where "inv_map m \<equiv> inverse_map (inj_part m)"

lemma inverse_map_Some_iff:
 "inj_map m \<Longrightarrow> (inverse_map m) x = Some y \<longleftrightarrow> m y = Some x"
  apply(simp add: inverse_map_def)
  apply(auto simp add: restrict_map_def inj_map_def)
  apply (smt domIff f_the_inv_into_f image_eqI mem_Collect_eq option.simps(3) ran_def)
  using the_inv_into_f_f apply fastforce
  by (smt domIff f_the_inv_into_f image_eqI mem_Collect_eq option.simps(3) ran_def)

lemma inverse_map_None_iff:
 "(inverse_map m) x = None \<longleftrightarrow> x \<notin> ran m"
  by(auto simp add: inverse_map_def)

lemma dom_inverse_map:
 "dom (inverse_map m) = ran m"
  by(auto simp add: inverse_map_def)

lemma ran_inverse_map:
 "inj_map m \<Longrightarrow> ran (inverse_map m) = dom m"
  by(auto simp add: ran_def inverse_map_Some_iff)

lemma inverse_map_m_m:
 "inj_map m \<Longrightarrow> (inverse_map m) \<circ>\<^sub>m m = Some |` (dom m)"
  apply(rule ext)
  apply(unfold restrict_map_def map_comp_def)
  apply(case_tac "m x")
   by(auto simp add: inverse_map_Some_iff)

lemma m_inverse_map_m:
 "inj_map m \<Longrightarrow> m \<circ>\<^sub>m (inverse_map m) = Some |`(ran m)"
  apply(rule ext)
  apply(unfold restrict_map_def map_comp_def)
  apply(case_tac "inverse_map m x")
   apply(auto)
  by(simp_all add: inverse_map_None_iff inverse_map_Some_iff ran_def)

lemma inverse_map_comp:
 "inj_map m1 \<Longrightarrow> inj_map m2 \<Longrightarrow> inverse_map m1 \<circ>\<^sub>m inverse_map m2 = inverse_map (m2 \<circ>\<^sub>m m1)"
  apply(rule ext)
  apply(case_tac "inverse_map (m2 \<circ>\<^sub>m m1) x")
   apply(simp_all)
   apply(simp add: inverse_map_None_iff map_comp_None_iff ran_def inverse_map_Some_iff)
   apply (metis (mono_tags, lifting) map_comp_simps(2))
  apply(simp add: inverse_map_Some_iff map_comp_Some_iff ran_def)
  apply(subst (asm) inverse_map_Some_iff)
  apply(drule_tac m'=m2 and m="m2 |`ran m1" in inj_map_le[rotated])
    apply(simp_all add: restrict_map_le inj_map_comp)
  apply(subst (asm) map_comp_Some_iff)
  by(auto)

lemma inverse_map_mono:
 "inj_map m2 \<Longrightarrow> m1 \<subseteq>\<^sub>m m2 \<Longrightarrow> inverse_map m1 \<subseteq>\<^sub>m inverse_map m2"
  apply(frule inj_map_le,simp)
  apply(simp add: map_le_def)
  apply(rule ballI)
  apply(simp add: dom_inverse_map ran_def)
  apply(drule_tac Q="inverse_map m1 a = inverse_map m2 a" in exE)
  apply(frule_tac m=m1 in domI)
   apply(drule_tac x=x in bspec,simp,simp)
   apply(subst (asm) inverse_map_Some_iff[where y=x and x=a,symmetric],simp)+
  by(simp_all)

lemma inv_map_Some_iff:
 "(inv_map m) x = Some y \<longleftrightarrow> m y = Some x \<and> y \<in> inj_dom m"
  by(auto simp add: inv_map_def inj_dom inj_part_inj inj_part_Some_iff inverse_map_Some_iff)

lemma inv_map_None_iff:
 "(inv_map m) x = None \<longleftrightarrow> x \<notin> inj_ran m"
  by(simp add: inv_map_def inverse_map_None_iff inj_ran_def)

lemma dom_inv_map:
 "dom (inv_map m) = ran (inj_part m)"
  by(simp add: inv_map_def dom_inverse_map)

lemma ran_inv_map:
 "ran (inv_map m) = dom (inj_part m)"
  by(simp add: inv_map_def ran_inverse_map inj_part_inj)

lemma inv_map_m_m:
 "(inv_map m) \<circ>\<^sub>m m = Some |` (dom (inj_part m))"
  apply(simp add: inv_map_def)
  apply(rule ext)
  apply(case_tac "(inverse_map (inj_part m) \<circ>\<^sub>m m) x")
   apply(simp add: restrict_map_def dom_def)
   apply(subst (asm)  map_comp_None_iff)
   apply(subst (asm)  inverse_map_None_iff)
   apply(drule_tac R="inj_part m x = None" in disjE)
     apply(simp add: inj_part_None_iff)
    apply(simp add: inj_part_def ran_def)
    apply(meson)
   apply(simp)
   apply(simp add: restrict_map_def dom_def)
   apply(subst (asm)  map_comp_Some_iff)
   apply(subst (asm)  inverse_map_Some_iff)
   apply(simp add: inj_part_inj)
  apply(rule conjI,rule impI)
   apply(simp add: inj_part_def)
   apply (metis domI domIff)
   by (metis (mono_tags, lifting) inj_part_Some_iff)

lemma m_inv_map_m:
 "m \<circ>\<^sub>m (inv_map m) = Some |`(ran (inj_part m))"
  apply(subst map_comp_restrict_ran[where A="dom (inj_part m)"])
   apply(simp add: ran_inv_map)
  apply(simp add: restrict_dom_m_is_m inj_part_le inv_map_def)
  apply(rule m_inverse_map_m)
  by(simp add: inj_part_inj)

lemma inv_map_comp':
 "inv_map m1 \<circ>\<^sub>m inv_map m2 \<subseteq>\<^sub>m inv_map (m2 \<circ>\<^sub>m m1)"
  apply(unfold inv_map_def)
  apply(simp add: inverse_map_comp inj_part_inj)
  apply(rule inverse_map_mono)
     apply(simp_all add: inj_part_inj inj_map_le inj_map_restrict)
  by(rule inj_part_comp')

lemma inv_map_comp:
 "inj_map (m2 |` ran m1) \<Longrightarrow> inv_map (m2 \<circ>\<^sub>m m1) = (inv_map m1)  \<circ>\<^sub>m inverse_map (m2 |` ran m1)"
  apply(unfold inv_map_def)
  apply(simp add: inverse_map_comp inj_part_inj)
  apply(rule_tac f=inverse_map in arg_cong)
  apply(simp add: inj_part_comp)
  apply(rule map_comp_restrict_ran)
  by(rule inj_ran_le)

lemma inv_map_mono:
 "inj_map m2 \<Longrightarrow> m1 \<subseteq>\<^sub>m m2 \<Longrightarrow> inv_map m1 \<subseteq>\<^sub>m inv_map m2"
  apply(simp add: inv_map_def)
  apply(rule inverse_map_mono)
   apply(simp add: inj_part_inj)
  apply(frule inj_map_le,simp)
  by(simp add: inj_map_is_inj_part)

end
