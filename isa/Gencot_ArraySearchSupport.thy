section \<open>Array Support\<close>

theory Gencot_ArraySearchSupport
  imports Gencot_ArrayObsrvSupport
begin

subsection \<open>Observation Functions for Searching\<close>

text \<open>
Searching in an array is usually done by traversing the array in ascending order and
returning the first element which satisfies a predicate \<open>p\<close> (or the element's index).
This can be generalized to traversing only an index-defined excerpt \<open>s\<close>, e.g., if the
traversal is done in steps greater than one. By combining \<open>s\<close> and \<open>p\<close> to a general
excerpt \<open>sp\<close> the search is equivalent to observing the first element (that with the
lowest index) in excerpt \<open>sp\<close>. Since \<open>sp\<close> may be empty, such an element need not exist.
\<close>

subsubsection \<open>Simple Search\<close>

text \<open>
The following derived observation functions are defined for searching in this way. The first
returns the index of the found element, the second returns the element itself.
\<close>

definition sp_indx_fst :: "(nat \<times> 'el \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> nat option"
  where "sp_indx_fst sp a \<equiv> 
         if sp_indx_set sp a = {} then None else Some (Min (sp_indx_set sp a))"
definition sp_elem_fst :: "(nat \<times> 'el \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> 'el option"
  where "sp_elem_fst sp a \<equiv> map_option (nth a) (sp_indx_fst sp a)"

text \<open>
Simplified forms where the excerpt is determined by element value alone.
Forms where the excerpt is determined by index or is the whole array are not
considered useful here, because they do not depend on the array content.
\<close>
definition p_indx_fst :: "('el \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> nat option"
  where "p_indx_fst p \<equiv> sp_indx_fst (p\<circ>snd)"
definition p_elem_fst :: "('el \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> 'el option"
  where "p_elem_fst p \<equiv> sp_elem_fst (p\<circ>snd)"

text \<open>
Alternative standalone definitions:
\<close>

lemma sp_indx_fst:
 "sp_indx_fst sp a = 
  (if \<forall>i. \<not> (iexcerpt sp a i) then None else Some (LEAST i. (iexcerpt sp a i)))"
  apply(simp add: sp_indx_fst_def sp_indx_set)
  by(simp add: Least_Min iexcerpt_def)

(* is this useful? *)
lemma sp_indx_fst':
 "sp_indx_fst sp a = map_option fst (find sp (enumerate 0 a))"
  apply(auto simp add: sp_indx_fst iexcerpt_def)
   apply(simp add: find_None_iff)
   apply(rule allI, rule allI)
   apply(simp add: in_set_enumerate_eq)
   apply(auto)[1]
  apply(rule sym)
  apply(simp add: find_Some_iff)
  apply(rule exI[where x="a ! (LEAST i. i < length a \<and> sp (i, a ! i))"])
  apply(rule exI[where x="LEAST i. i < length a \<and> sp (i, a ! i)"])
  apply(drule_tac Q="sp (i, a ! i)" in conjI,simp)
  apply(drule exI[where P="\<lambda>x. x < length a \<and> sp (x, a ! x)"])
  apply(drule LeastI_ex)
  apply(auto simp add: nth_enumerate_eq)
  apply(frule not_less_Least)
  by(auto)

lemma sp_elem_fst:
 "sp_elem_fst sp a = 
  (if \<forall>i. \<not> (iexcerpt sp a i) then None else Some (nth a (LEAST i. (iexcerpt sp a i))))"
  apply(unfold sp_elem_fst_def)
  by(simp add: sp_indx_fst)

lemma p_indx_fst:
 "p_indx_fst p a = 
  (if \<forall>i. vld a i \<longrightarrow> \<not> p (a!i) then None else Some (LEAST i. vld a i \<and> p (a!i)))"
  apply(unfold p_indx_fst_def)
  by(auto simp add: sp_indx_fst iexcerpt_def)

lemma p_elem_fst:
 "p_elem_fst p a = 
  (if \<forall>i. vld a i \<longrightarrow> \<not> p (a!i) then None else Some (a ! (LEAST i. vld a i \<and> p (a!i))))"
  apply(unfold p_elem_fst_def)
  by(auto simp add: sp_elem_fst iexcerpt_def)

text \<open>
Relating \<open>sp_indx_fst\<close> and \<open>sp_elem_fst\<close>
\<close>

lemma sp_elem_fst_indx:
 "sp_elem_fst sp a = map_option (nth a) (sp_indx_fst sp a)"
  by(simp add: sp_elem_fst sp_indx_fst)

text \<open>
Rules for the search result.
\<close>

lemma sp_indx_fst_valid: 
 "sp_indx_fst sp a = Some i \<Longrightarrow> 
  i < length a"
  apply(simp add: sp_indx_fst)
  apply(case_tac "\<forall>i. \<not> (iexcerpt sp a i) ",simp)
   apply(simp, simp add: iexcerpt_def)
  by(drule LeastI_ex,simp)
lemma sp_indx_fst_satisfies_sp: 
 "sp_indx_fst sp a = Some i \<Longrightarrow> 
  sp (i,nth a i)"
  apply(simp add: sp_indx_fst)
  apply(case_tac "\<forall>i. \<not> (iexcerpt sp a i) ",simp)
   apply(simp, simp add: iexcerpt_def)
  by(drule LeastI_ex,simp)
lemma sp_indx_fst_isleast_sp: 
 "sp_indx_fst sp a = Some i \<Longrightarrow> 
  \<forall> k. k < length a \<and> sp (k,nth a k) \<and> k < i \<longrightarrow> \<not> sp (k,nth a k)"
  apply(simp add: sp_indx_fst)
  apply(case_tac "\<forall>i. \<not> (iexcerpt sp a i) ",simp)
  apply(simp, simp add: iexcerpt_def)
  by (metis (no_types, lifting) LeastI less_le_trans linorder_not_le not_less_Least)
lemma sp_indx_fst_ismin_sp: 
 "sp_indx_fst sp a = Some i \<Longrightarrow> 
  i = Min (sp_indx_set sp a)"
  apply(simp add: sp_indx_fst_def)
  by(case_tac "sp_indx_set sp a = {}",simp_all)
lemma sp_indx_fst_notfound_iff: 
 "(sp_indx_fst sp a = None) = (\<forall> i. i < length a \<longrightarrow> \<not> sp (i,nth a i))"
  by(simp add: sp_indx_fst iexcerpt_def)
lemma sp_elem_fst_indx_fst:
 "\<lbrakk>sp_indx_fst sp a = Some i; e = nth a i\<rbrakk> \<Longrightarrow> 
  sp_elem_fst sp a = Some e"
  by(simp add: sp_elem_fst_def)

lemma p_indx_fst_valid: 
 "p_indx_fst p a = Some i \<Longrightarrow> 
  i < length a"
  by(simp add: p_indx_fst_def sp_indx_fst_valid)
lemma p_indx_fst_satisfies_p: 
 "p_indx_fst p a = Some i \<Longrightarrow> 
  p (nth a i)"
  apply(simp add: p_indx_fst_def)
  by(drule sp_indx_fst_satisfies_sp,simp)
lemma p_indx_fst_isleast_p: 
 "p_indx_fst p a = Some i \<Longrightarrow> 
  \<forall> k. k < length a \<and> p (nth a k) \<and> k < i \<longrightarrow> \<not> p (nth a k)"
  apply(simp add: p_indx_fst_def)
  by(drule sp_indx_fst_isleast_sp,simp)
lemma p_indx_fst_ismin_p: 
 "p_indx_fst p a = Some i \<Longrightarrow> 
  i = Min (p_indx_set p a)"
  apply(simp add: p_indx_fst_def p_indx_set_def)
  by(drule sp_indx_fst_ismin_sp,simp)
lemma p_indx_fst_notfound_iff: 
 "(p_indx_fst p a = None) = (\<forall> i. i < length a \<longrightarrow> \<not> p (nth a i))"
  by(simp add: p_indx_fst iexcerpt_def)
lemma p_elem_fst_indx_fst:
 "\<lbrakk>p_indx_fst p a = Some i; e = nth a i\<rbrakk> \<Longrightarrow> 
  p_elem_fst p a = Some e"
  by(simp add: p_elem_fst_def p_indx_fst_def sp_elem_fst_indx_fst)

text \<open>
The search result index for a union of excerpts is the minimum of both search result indexes.
There is no union rule for \<open>sp_elem_fst\<close> and \<open>p_elem_fst\<close> because the information about the 
order of both results in the array is lost.
\<close>
lemma sp_indx_fst_SP_union:
 "sp_indx_fst (sp1 \<squnion> sp2) a = combine_options min (sp_indx_fst sp1 a) (sp_indx_fst sp2 a)"
  apply(auto simp add: sp_indx_fst iexcerpt_def)
     apply(rule arg_cong[where f=Least],blast)+
  apply(subst Least_Min,simp,rule_tac x=i in exI,simp)
  apply(subst Least_Min,simp,rule_tac x=i in exI,simp)
   apply(subst Least_Min,simp,rule_tac x=ia in exI,simp)
  apply(subst Min.union[symmetric],auto) apply(rule arg_cong[where f=Min],blast)
  apply(subst Least_Min,simp,rule_tac x=i in exI,simp)
  apply(subst Least_Min,simp,rule_tac x=i in exI,simp)
   apply(subst Least_Min,simp,rule_tac x=ia in exI,simp)
  apply(subst Min.union[symmetric],auto) apply(rule arg_cong[where f=Min],blast)
  done
lemma p_indx_fst_P_union:
 "p_indx_fst (p1 \<squnion> p2) a = combine_options min (p_indx_fst p1 a) (p_indx_fst p2 a)"
  apply(simp add: p_indx_fst_def un_comp_pred)
  by(rule sp_indx_fst_SP_union)

text \<open>
If the excerpt covers all indices the search covers the whole array.
\<close>

lemma sp_to_p_indx_fst:
 "\<forall>i<length a. sp (i,nth a i) = p (nth a i) \<Longrightarrow>
  sp_indx_fst sp a = p_indx_fst p a"
  apply(auto simp add: p_indx_fst_def sp_indx_fst_def sp_indx_set iexcerpt_def)
  apply(rule arg_cong[where f=Min,symmetric])
  by(rule Collect_cong,auto)

lemma sp_to_p_elem_fst:
 "\<forall>i<length a. sp (i,nth a i) = p (nth a i) \<Longrightarrow>
  sp_elem_fst sp a = p_elem_fst p a"
  apply(simp add: sp_elem_fst_def p_elem_fst_def)
  apply(rule arg_cong[where f="map_option ((!) a)"])
  by(fold p_indx_fst_def,simp add:  sp_to_p_indx_fst)

subsubsection \<open>Parameterized Search\<close>

text \<open>
If the search predicate \<open>p\<close> depends on a parameter, the search may return an index
or element for every parameter value. This is equivalent to a map from parameter values to
index or element values. The search predicate is equivalent to a relation \<open>r\<close>
between parameter values and array elements. The index based excerpt \<open>s\<close> is not 
parameterized, since it is intended to be a fixed excerpt in which to search. All 
functions for parameterized search are defined for pairs \<open>sr = (s,r)\<close> of a fixed 
index based excerpt \<open>s\<close> and a parameterized search predicate \<open>r\<close>. The function \<open>rexcrp\<close>
can be used to convert such pairs to a parameterized general excerpt.

The following functions are derived observations for observing maps resulting from 
parameterized search based on such pairs.
\<close>

definition sr_indx_fst_map :: "(nat \<Rightarrow> bool) \<times> ('t \<Rightarrow> 'el \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> 't \<rightharpoonup> nat"
  where "sr_indx_fst_map sr a \<equiv> \<lambda>x. sp_indx_fst (rexcrp sr x) a"
definition sr_elem_fst_map :: "(nat \<Rightarrow> bool) \<times> ('t \<Rightarrow> 'el \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> 't \<rightharpoonup> 'el"
  where "sr_elem_fst_map sr a \<equiv> \<lambda>x. sp_elem_fst (rexcrp sr x) a"

text \<open>
Simplified forms where the excerpt is determined by element value alone.
\<close>
definition r_indx_fst_map :: "('t \<Rightarrow> 'el \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> 't \<rightharpoonup> nat"
  where "r_indx_fst_map r \<equiv> sr_indx_fst_map (\<top>,r)"
definition r_elem_fst_map :: "('t \<Rightarrow> 'el \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> 't \<rightharpoonup> 'el"
  where "r_elem_fst_map r \<equiv> sr_elem_fst_map (\<top>,r)"

lemma r_indx_fst_map_p_indx_fst:
 "r_indx_fst_map r a x = p_indx_fst (r x) a"
  by(simp add: r_indx_fst_map_def sr_indx_fst_map_def rexcrp_def p_indx_fst_def pred_prod_top1)
  
lemma r_elem_fst_map_p_elem_fst:
 "r_elem_fst_map r a x = p_elem_fst (r x) a"
  by(simp add: r_elem_fst_map_def sr_elem_fst_map_def rexcrp_def p_elem_fst_def pred_prod_top1)

text \<open>
Alternative standalone definitions:
\<close>
lemma sr_indx_fst_map:
 "sr_indx_fst_map sr a = 
  (\<lambda>x. if \<forall>i. \<not> (rexcerpt sr x a i) then None else Some (LEAST i. (rexcerpt sr x a i)))"
  by(auto simp add: sr_indx_fst_map_def sp_indx_fst rexcerpt_def)

lemma sr_elem_fst_map:
 "sr_elem_fst_map sr a = 
  (\<lambda>x. if \<forall>i. \<not> (rexcerpt sr x a i) then None else Some (nth a (LEAST i. (rexcerpt sr x a i))))"
  by(auto simp add: sr_elem_fst_map_def sp_elem_fst rexcerpt_def)

lemma r_indx_fst_map:
 "r_indx_fst_map r a = 
  (\<lambda>x. if \<forall>i. vld a i \<longrightarrow> \<not> r x (a!i) then None else Some (LEAST i. vld a i \<and> r x (a!i)))"
  apply(unfold r_indx_fst_map_def)
  apply(simp add: sr_indx_fst_map)
  by(rule ext, simp add: rexcerpt)

lemma r_elem_fst_map:
 "r_elem_fst_map r a = 
  (\<lambda>x. if \<forall>i. vld a i \<longrightarrow> \<not> r x (a!i) then None else Some (a ! (LEAST i. vld a i \<and> r x (a!i))))"
  apply(unfold r_elem_fst_map_def)
  by(auto simp add: sr_elem_fst_map rexcerpt)

text \<open>
Rules for the search result.
\<close>

lemma sr_indx_fst_map_valid: 
 "sr_indx_fst_map sr a x = Some i \<Longrightarrow> 
  i < length a"
  by(simp add: sr_indx_fst_map_def sp_indx_fst_valid)
lemma sr_indx_fst_map_satisfies_sr:
 "sr_indx_fst_map (s,r) a x = Some i \<Longrightarrow> 
  (s i) \<and> (r x (nth a i))"
  apply(simp add: sr_indx_fst_map_def)
  apply(drule sp_indx_fst_satisfies_sp)
  by(simp add: rexcrp_def)
lemma sr_indx_fst_map_isleast_sr: 
 "sr_indx_fst_map (s,r) a x = Some i \<Longrightarrow> 
  \<forall> k. k < length a \<and> s k \<and> k < i \<longrightarrow> \<not> r x (nth a k)"
  apply(simp add: sr_indx_fst_map_def)
  apply(drule sp_indx_fst_isleast_sp)
  by(auto simp add: rexcrp_def)
lemma sr_indx_fst_map_None_iff: 
 "(sr_indx_fst_map (s,r) a x = None) = (\<forall> i. vld a i \<longrightarrow> s i \<longrightarrow> \<not> r x (nth a i))"
  by(simp add: sr_indx_fst_map_def sp_indx_fst_notfound_iff rexcrp_def)
lemma sr_elem_fst_map_indx_fst_map:
 "\<lbrakk>sr_indx_fst_map sr a x = Some i; e = nth a i\<rbrakk> \<Longrightarrow> 
  sr_elem_fst_map sr a x = Some e"
  apply(simp add: sr_elem_fst_map_def sr_indx_fst_map_def)
  by(drule sp_elem_fst_indx_fst,simp_all)

text \<open>
The search result index for a union of index excerpts is the minimum of both search result indexes.
\<close>
lemma sr_indx_fst_map_S_union:
 "sr_indx_fst_map (s1 \<squnion> s2, r) a x = 
  combine_options min (sr_indx_fst_map (s1,r) a x) (sr_indx_fst_map (s2,r) a x)"
  apply(simp add: sr_indx_fst_map_def)
  apply(subst sp_indx_fst_SP_union[symmetric])
  apply(rule_tac x=a in fun_cong)
  apply(rule_tac f=sp_indx_fst in arg_cong)
  by(auto simp add: rexcrp_def)

text \<open>
Function \<open>sr_elem_fst_map\<close> is mainly equivalent to the composition of
\<open>sr_indx_fst_map\<close> and \<open>sp_elem_map\<close>. In this composition \<open>sp_elem_map\<close> can
be reduced to the excerpt where \<open>sr\<close> is satisfied for some parameter value. This is 
expressed by defining a function \<open>sr_some\<close> which transforms the pair \<open>sr\<close> to a 
corresponding predicate \<open>sp\<close> which can be used as excerpt predicate. 

Since \<open>sr_indx_fst_map\<close> returns only valid indexes where the element satisfies
the pair \<open>sr\<close> for some parameter value the composition does not restrict the maps
and \<open>elem_map\<close> can be used instead of \<open>sp_elem_map\<close>.
\<close>

definition sr_some :: "(nat \<Rightarrow> bool) \<times> ('t \<Rightarrow> 'el \<Rightarrow> bool) \<Rightarrow> (nat \<times> 'el \<Rightarrow> bool)"
  where "sr_some sr \<equiv> \<lambda>(i,e). \<exists> x. rexcrp sr x (i,e)"
definition r_some :: "('t \<Rightarrow> 'el \<Rightarrow> bool) \<Rightarrow> 'el \<Rightarrow> bool"
  where "r_some r \<equiv> \<lambda>e. \<exists> x. r x e"

lemma r_some_sr_some: 
 "r_some r \<circ> snd = sr_some (\<top>, r)"
  apply(simp add: r_some_def sr_some_def split_def rexcrp_def)
  by(rule ext,rule comp_apply)

lemma sr_elem_fst_map_indx: 
 "(sr_elem_fst_map sr a) = 
  (sp_elem_map (sr_some sr) a) \<circ>\<^sub>m (sr_indx_fst_map sr a)"
  apply(simp add: sr_elem_fst_map_def sr_indx_fst_map_def)
  apply(simp add: sp_elem_fst_indx)
  apply(rule ext)
  apply(simp add: sp_elem_map sr_some_def iexcerpt_def map_comp_def)
  apply(case_tac "sp_indx_fst (rexcrp sr x) a",simp)
  apply(frule sp_indx_fst_valid,frule sp_indx_fst_satisfies_sp)
  by(simp,rule exI)

lemma ran_sr_indx_fst_map: 
 "ran (sr_indx_fst_map sr a) \<subseteq> dom (sp_elem_map (sr_some sr) a)"
  apply(simp add: ran_def)
  apply(rule subsetI,simp)
  apply(erule exE)
  apply(simp add: sr_indx_fst_map_def)
  apply(frule sp_indx_fst_satisfies_sp,drule sp_indx_fst_valid)
  apply(rule_tac b="a ! x" in domI)
  apply(simp add: sp_elem_map sr_some_def iexcerpt_def)
  by(rule exI)

lemma dom_sr_indx_fst_map:
 "dom (sr_indx_fst_map sr a) = dom (sr_elem_fst_map sr a)"
  apply(simp add: sr_elem_fst_map_def sr_indx_fst_map_def dom_def)
  apply(rule Collect_cong)
  by(auto simp add: sp_elem_fst_indx)

lemma sr_elem_fst_map_indx': 
 "(sr_elem_fst_map sr a) = 
  (elem_map a) \<circ>\<^sub>m (sr_indx_fst_map sr a)"
  apply(simp add: sr_elem_fst_map_indx)
  apply(rule sym)
  apply(rule map_comp_restrict_ran')
  apply(rule ran_sr_indx_fst_map)
  by(auto simp add: sp_elem_map sr_some_def elem_map iexcerpt_def map_le_def)

lemma r_elem_fst_map_indx:
 "(r_elem_fst_map r a) = 
  (p_elem_map (r_some r) a) \<circ>\<^sub>m (r_indx_fst_map r a)"
  apply(simp add: r_elem_fst_map_def p_elem_map_def r_indx_fst_map_def)
  by(simp add: r_some_sr_some sr_elem_fst_map_indx)

lemma ran_r_indx_fst_map: 
 "ran (r_indx_fst_map r a) \<subseteq> dom (p_elem_map (r_some r) a)"
  apply(simp add: p_elem_map_def r_indx_fst_map_def)
  by(simp add: r_some_sr_some ran_sr_indx_fst_map)

lemma dom_r_indx_fst_map:
 "dom (r_indx_fst_map r a) = dom (r_elem_fst_map r a)"
  apply(simp add: r_elem_fst_map_def r_indx_fst_map_def)
  by(simp add: r_some_sr_some dom_sr_indx_fst_map)

lemma r_elem_fst_map_indx': 
 "(r_elem_fst_map r a) = 
  (elem_map a) \<circ>\<^sub>m (r_indx_fst_map r a)"
  by(simp add: r_elem_fst_map_def r_indx_fst_map_def sr_elem_fst_map_indx')

subsubsection \<open>Derived Maps for Parameterized Search\<close>

text \<open>
From the maps \<open>sr_indx_fst_map\<close> and \<open>sr_elem_fst_map\<close> maps are derived by inverting, domain,
range, and cadinality.
\<close>

definition sr_indx_fst_inv :: "(nat \<Rightarrow> bool) \<times> ('t \<Rightarrow> 'el \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> nat \<rightharpoonup> 't"
  where "sr_indx_fst_inv sr a \<equiv> inv_map (sr_indx_fst_map sr a)"
definition sr_elem_fst_inv :: "(nat \<Rightarrow> bool) \<times> ('t \<Rightarrow> 'el \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> 'el \<rightharpoonup> 't"
  where "sr_elem_fst_inv sr a \<equiv> inv_map (sr_elem_fst_map sr a)"
definition sr_parm_fst_set :: "(nat \<Rightarrow> bool) \<times> ('t \<Rightarrow> 'el \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> 't set"
  where "sr_parm_fst_set sr a \<equiv> dom (sr_indx_fst_map sr a)"
definition sr_indx_fst_set :: "(nat \<Rightarrow> bool) \<times> ('t \<Rightarrow> 'el \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> nat set"
  where "sr_indx_fst_set sr a \<equiv> ran (sr_indx_fst_map sr a)"
definition sr_elem_fst_set :: "(nat \<Rightarrow> bool) \<times> ('t \<Rightarrow> 'el \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> 'el set"
  where "sr_elem_fst_set sr a \<equiv> ran (sr_elem_fst_map sr a)"
definition sr_parm_fst_num :: "(nat \<Rightarrow> bool) \<times> ('t \<Rightarrow> 'el \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> nat"
  where "sr_parm_fst_num sr a \<equiv> card (sr_parm_fst_set sr a)"
definition sr_indx_fst_num :: "(nat \<Rightarrow> bool) \<times> ('t \<Rightarrow> 'el \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> nat"
  where "sr_indx_fst_num sr a \<equiv> card (sr_indx_fst_set sr a)"
definition sr_elem_fst_num :: "(nat \<Rightarrow> bool) \<times> ('t \<Rightarrow> 'el \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> nat"
  where "sr_elem_fst_num sr a \<equiv> card (sr_elem_fst_set sr a)"

definition r_indx_fst_inv :: "('t \<Rightarrow> 'el \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> nat \<rightharpoonup> 't"
  where "r_indx_fst_inv r \<equiv> sr_indx_fst_inv (\<top>,r)"
definition r_elem_fst_inv :: "('t \<Rightarrow> 'el \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> 'el \<rightharpoonup> 't"
  where "r_elem_fst_inv r \<equiv> sr_elem_fst_inv (\<top>,r)"
definition r_parm_fst_set :: "('t \<Rightarrow> 'el \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> 't set"
  where "r_parm_fst_set r \<equiv> sr_parm_fst_set (\<top>,r)"
definition r_indx_fst_set :: "('t \<Rightarrow> 'el \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> nat set"
  where "r_indx_fst_set r \<equiv> sr_indx_fst_set (\<top>,r)"
definition r_elem_fst_set :: "('t \<Rightarrow> 'el \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> 'el set"
  where "r_elem_fst_set r \<equiv> sr_elem_fst_set (\<top>,r)"
definition r_parm_fst_num :: "('t \<Rightarrow> 'el \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> nat"
  where "r_parm_fst_num r \<equiv> sr_parm_fst_num (\<top>,r)"
definition r_indx_fst_num :: "('t \<Rightarrow> 'el \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> nat"
  where "r_indx_fst_num r \<equiv> sr_indx_fst_num (\<top>,r)"
definition r_elem_fst_num :: "('t \<Rightarrow> 'el \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> nat"
  where "r_elem_fst_num r \<equiv> sr_elem_fst_num (\<top>,r)"

subsubsection \<open>Injective Search\<close>

text \<open>
If for an excerpt relation every array entry is specified by atmost one parameter value the 
map \<open>sr_indx_fst_map\<close> from parameter values to array indexes can be inverted. 

The predicates \<open>sr_injective\<close> and \<open>r_injective\<close> are defined for this property. 
The predicate \<open>rel_injective\<close> states injectivity for arbitrary relations.
\<close>

definition sr_injective :: "(nat \<Rightarrow> bool) \<times> ('t \<Rightarrow> 'el \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> bool"
  where "sr_injective sr a \<equiv> \<forall> i x y. rexcerpt sr x a i \<longrightarrow> rexcerpt sr y a i \<longrightarrow> x = y"
definition r_injective :: "('t \<Rightarrow> 'el \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> bool"
  where "r_injective r a \<equiv> sr_injective (\<top>,r) a"
definition rel_injective :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
  where "rel_injective r \<equiv> single_valuedp (conversep r)"

lemma r_injective:
 "r_injective r a = (\<forall> i x y. iexcerpt ((r x)\<circ>snd) a i \<longrightarrow> iexcerpt ((r y)\<circ>snd) a i \<longrightarrow> x = y)"
  by(simp add: r_injective_def sr_injective_def rexcerpt iexcerpt_def)

lemma rel_injective_r_injective:
 "rel_injective r \<Longrightarrow> r_injective r a"
  by(auto simp add: rel_injective_def r_injective iexcerpt_def single_valuedp_def)

lemma r_injective_sr_injective:
 "r_injective r a \<Longrightarrow> sr_injective (s,r) a"
  by(auto simp add: r_injective sr_injective_def rexcerpt iexcerpt_def)

lemma sr_injective_le:
 "\<lbrakk>sr_injective sr2 a; rexcrp sr1 \<le> rexcrp sr2\<rbrakk> \<Longrightarrow> sr_injective sr1 a"
  apply(auto simp add: sr_injective_def rexcerpt rexcrp_def)
  by(drule_tac x=i in spec,clarsimp simp add: le_rel)

lemma r_injective_le:
 "\<lbrakk>r_injective r2 a; r1 \<le> r2\<rbrakk> \<Longrightarrow> r_injective r1 a"
  apply(simp add: r_injective_def)
  by(erule sr_injective_le,simp add: rexcrp_def le_rel)

lemma sr_injective_union:
 "\<lbrakk>sr_injective (s1 \<squnion> s2,r) a\<rbrakk> \<Longrightarrow> sr_injective (s1,r) a \<and> sr_injective (s2,r) a"
  by(auto simp add: sr_injective_def rexcerpt rexcrp_def)

lemma inj_sr_indx_fst_map: 
 "sr_injective sr a \<Longrightarrow> inj_map (sr_indx_fst_map sr a)"
  apply(simp add: sr_injective_def inj_map_def sr_indx_fst_map_def)
  apply(rule inj_onI)
  apply(auto simp add: sp_indx_fst,fold rexcerpt_def)
  apply(case_tac "\<forall>i. \<not> rexcerpt sr x a i",simp_all)
  apply(case_tac "\<forall>i. \<not> rexcerpt sr y a i",simp_all)
  using LeastI_ex by metis

lemma inj_r_indx_fst_map: 
 "r_injective r a \<Longrightarrow> inj_map (r_indx_fst_map r a)"
  apply(simp add: r_indx_fst_map_def)
  apply(rule inj_sr_indx_fst_map)
  by(simp add: r_injective_def sr_injective_def pred_prod_top1 rexcrp_def)

text \<open>
More general, if \<open>sr_injective\<close> holds for a pair \<open>(s,r)\<close>, then every index in \<open>s\<close> can be 
mapped to the unique parameter value which finds the index. The corresponding map is 
constructed by the following functions. 
\<close>

definition sr_indx_all_inv :: "(nat \<Rightarrow> bool) \<times> ('t \<Rightarrow> 'el \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> nat \<rightharpoonup> 't"
  where "sr_indx_all_inv sr a i \<equiv> if iexcerpt (sr_some sr) a i then Some (THE x. (snd sr) x (nth a i)) else None"

definition r_indx_all_inv :: "('t \<Rightarrow> 'el \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> nat \<rightharpoonup> 't"
  where "r_indx_all_inv r \<equiv> sr_indx_all_inv (\<top>,r)"

lemma sr_indx_all_inv_Some_iff:
 "sr_injective sr a \<Longrightarrow>
  (sr_indx_all_inv sr a i = Some x) =
  ((snd sr) x (nth a i) \<and> vld a i \<and> (fst sr) i)"
  apply(auto simp add: sr_indx_all_inv_def sr_injective_def sr_some_def rexcerpt iexcerpt_def rexcrp_def)
  by(rule_tac a=xa in theI,simp_all)

lemma sr_indx_all_inv_None_iff:
 "sr_injective sr a \<Longrightarrow>
  (sr_indx_all_inv sr a i = None) =
  (\<forall>x. \<not> ((snd sr) x (nth a i) \<and> vld a i \<and> (fst sr) i))"
  by(auto simp add: sr_indx_all_inv_def sr_injective_def sr_some_def rexcrp_def iexcerpt_def)
lemma sr_indx_all_inv_None_iff':
 "sr_injective sr a \<Longrightarrow>
  (sr_indx_all_inv sr a i = None) =
  (\<forall>x. vld a i \<longrightarrow> (fst sr) i \<longrightarrow> \<not> (snd sr) x (nth a i))"
  by(auto simp add: sr_indx_all_inv_def sr_injective_def sr_some_def rexcrp_def iexcerpt_def)

lemma r_indx_all_inv_Some_iff:
 "r_injective r a \<Longrightarrow>
  (r_indx_all_inv r a i = Some x) =
  (r x (nth a i) \<and> vld a i)"
  by(simp add: r_indx_all_inv_def r_injective_def sr_indx_all_inv_Some_iff)

lemma r_indx_all_inv_None_iff:
 "r_injective r a \<Longrightarrow>
  (r_indx_all_inv r a i = None) =
  (\<forall>x. \<not> (r x (nth a i) \<and> vld a i))"
  by(simp add: r_indx_all_inv_def r_injective_def sr_indx_all_inv_None_iff)

subsection \<open>Arrays with Distinct Elements\<close>

subsubsection \<open>Unique Excerpts\<close>

text \<open>
If an array excerpt contains atmost one index, the excerpt specifies its content in a unique way.
The predicates \<open>sp_uniq\<close> and \<open>p_uniq\<close> are defined for this property. 
\<close>

definition sp_uniq :: "(nat \<times> 'el \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> bool"
  where "sp_uniq sp a \<equiv> \<forall>i j. iexcerpt sp a i \<longrightarrow> iexcerpt sp a j \<longrightarrow> i = j"
definition p_uniq :: "('el \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> bool"
  where "p_uniq p a \<equiv> sp_uniq (p\<circ>snd) a"

lemma sp_indx_fst_sp_uniq:
 "\<lbrakk>sp_uniq sp a; iexcerpt sp a i\<rbrakk> \<Longrightarrow> sp_indx_fst sp a = Some i"
  apply(simp add: sp_indx_fst sp_uniq_def)
  using LeastI_ex by blast
lemma sp_elem_map_sp_uniq: 
 "\<lbrakk>sp_uniq sp a; sp_indx_fst sp a = Some i\<rbrakk> \<Longrightarrow> sp_elem_map sp a = [i \<mapsto> nth a i]"
  apply(simp add: sp_indx_fst sp_uniq_def sp_elem_map)
  apply(case_tac "\<forall>i. \<not> iexcerpt sp a i",simp_all)
  apply(drule LeastI_ex)
  by(auto simp add: iexcerpt_def)
lemma sp_indx_set_sp_uniq: 
 "\<lbrakk>sp_uniq sp a; sp_indx_fst sp a = Some i\<rbrakk> \<Longrightarrow> sp_indx_set sp a = {i}"
  by(simp add: sp_indx_set_def sp_elem_map_sp_uniq)
lemma sp_elem_set_sp_uniq: 
 "\<lbrakk>sp_uniq sp a; sp_elem_fst sp a = Some e\<rbrakk> \<Longrightarrow> sp_elem_set sp a = {e}"
  apply(simp add: sp_elem_set_def sp_elem_fst_def)
  using sp_elem_map_sp_uniq by fastforce

lemma p_indx_fst_p_uniq:
 "\<lbrakk>p_uniq p a; iexcerpt (p\<circ>snd) a i\<rbrakk> \<Longrightarrow> p_indx_fst p a = Some i"
  by(simp add: p_indx_fst_def p_uniq_def sp_indx_fst_sp_uniq)
lemma p_elem_map_p_uniq: 
 "\<lbrakk>p_uniq p a; p_indx_fst p a = Some i\<rbrakk> \<Longrightarrow> p_elem_map p a = [i \<mapsto> nth a i]"
  by(simp add: p_indx_fst_def p_uniq_def p_elem_map_def sp_elem_map_sp_uniq)
lemma p_indx_set_p_uniq: 
 "\<lbrakk>p_uniq p a; p_indx_fst p a = Some i\<rbrakk> \<Longrightarrow> p_indx_set p a = {i}"
  by(simp add: p_uniq_def p_indx_fst_def p_indx_set_def sp_indx_set_sp_uniq)
lemma p_elem_set_p_uniq: 
 "\<lbrakk>p_uniq p a; p_elem_fst p a = Some e\<rbrakk> \<Longrightarrow> p_elem_set p a = {e}"
  by(simp add: p_uniq_def p_elem_fst_def p_elem_set_def sp_elem_set_sp_uniq)

subsubsection \<open>Unique Search for Elements\<close>

text \<open>
If for a pair \<open>sr\<close> the excerpt relation \<open>rexcrp sr\<close> is unique for every parameter value, 
the parameter values are unique specifications for the elements in the excerpt \<open>sr_some sr\<close>. 
By using \<open>sr\<close> for a parameterized search it is possible to find all elements in the excerpt \<open>sr_some sr\<close>. 

The predicates \<open>sr_uniq\<close> and \<open>r_uniq\<close> are defined for this property. The predicates \<open>sr_bijective\<close> 
and \<open>r_bijective\<close> combine it with the corresponding injectivity.
\<close>

definition sr_uniq :: "(nat \<Rightarrow> bool) \<times> ('t \<Rightarrow> 'el \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> bool"
  where "sr_uniq sr a \<equiv> \<forall> x. sp_uniq (rexcrp sr x) a"
definition sr_bijective :: "(nat \<Rightarrow> bool) \<times> ('t \<Rightarrow> 'el \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> bool"
  where "sr_bijective sr a \<equiv> sr_uniq sr a \<and> sr_injective sr a"
definition r_uniq :: "('t \<Rightarrow> 'el \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> bool"
  where "r_uniq r \<equiv> sr_uniq (\<top>,r)"
definition r_bijective :: "('t \<Rightarrow> 'el \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> bool"
  where "r_bijective r a \<equiv> r_uniq r a \<and> r_injective r a"

lemma r_uniq_p_uniq:
 "r_uniq r a \<equiv> \<forall> x. p_uniq (r x) a"
  by(simp add: r_uniq_def sr_uniq_def p_uniq_def rexcrp_def pred_prod_top1)

text \<open>
If \<open>sr_uniq\<close> holds for a pair of excerpts and position \<open>i\<close> is related to parameter \<open>x\<close> then
\<open>i\<close> is found by searching for \<open>x\<close>.
\<close>

lemma sr_indx_fst_sr_uniq:
 "\<lbrakk>sr_uniq sr a; rexcerpt sr x a i\<rbrakk> \<Longrightarrow> sr_indx_fst_map sr a x = Some i"
  by(simp add: sr_uniq_def sr_indx_fst_map_def rexcerpt_def sp_indx_fst_sp_uniq)
lemma p_indx_fst_r_uniq:
 "\<lbrakk>r_uniq r a; iexcerpt ((r x)\<circ>snd) a i\<rbrakk> \<Longrightarrow> r_indx_fst_map r a x = Some i"
  apply(simp add: p_uniq_def r_uniq_def r_indx_fst_map_def)
  by(simp add: sr_uniq_def sr_indx_fst_sr_uniq rexcerpt_def rexcrp_def pred_prod_top1)

text \<open>
If \<open>sr_uniq\<close> holds for a pair of excerpts then it holds for every pair of sub excerpts.
Same for \<open>sr_bijective\<close>.
\<close>
lemma sr_uniq_le:
 "\<lbrakk>sr_uniq sr2 a; rexcrp sr1 \<le> rexcrp sr2\<rbrakk> \<Longrightarrow> sr_uniq sr1 a"
  by(auto simp add: sr_uniq_def sp_uniq_def iexcerpt_def)
lemma sr_bijective_le:
 "\<lbrakk>sr_bijective sr2 a; rexcrp sr1 \<le> rexcrp sr2\<rbrakk> \<Longrightarrow> sr_bijective sr1 a"
  by(auto simp add: sr_bijective_def sr_uniq_le sr_injective_le)
lemma r_uniq_le:
 "\<lbrakk>r_uniq r2 a; r1 \<le> r2\<rbrakk> \<Longrightarrow> r_uniq r1 a"
  by(auto simp add: r_uniq_p_uniq p_uniq_def sp_uniq_def iexcerpt_def)
lemma r_bijective_le:
 "\<lbrakk>r_bijective r2 a; r1 \<le> r2\<rbrakk> \<Longrightarrow> r_bijective r1 a"
  by(auto simp add: r_bijective_def r_uniq_le r_injective_le)

text \<open>
\<open>sr_uniq\<close> holds for every excerpt pair where the index excerpt is a singleton.
\<close>
lemma sr_uniq_isingl:
 "sr_uniq (isingl i,r) a"
  by(simp add: sr_uniq_def sp_uniq_def iexcerpt_def rexcrp_def isingl)

text \<open>
If \<open>sr_uniq\<close> holds for the union of disjoint index excerpts and a search relation then every element can be 
found in only one of both index excerpts.
\<close>

lemma sr_uniq_union:
 "\<lbrakk>sr_uniq (s1 \<squnion> s2, r) a; s1 \<sqinter> s2 = \<bottom>; sr_indx_fst_map (s1,r) a x = Some i\<rbrakk> \<Longrightarrow> 
  sr_indx_fst_map (s2,r) a x = None"
  apply(simp add: sr_indx_fst_map)
  apply(case_tac "\<forall>i. \<not> rexcerpt (s1,r) x a i",simp_all)
  apply(drule LeastI_ex)
  apply(auto simp add: sr_uniq_def sp_uniq_def,fold rexcerpt_def, simp add: rexcerpt)
  apply(drule_tac x=xa in disjoint_pred)
  by(auto simp add: iexcerpt_def)

text \<open>
If \<open>sr_uniq\<close> is false for the union of disjoint index excerpts and a search relation,
but holds for both, then there is an element which can be found in both index excerpts.
\<close>

lemma sr_non_uniq_union:
 "\<lbrakk>\<not> sr_uniq (s1 \<squnion> s2, r) a; s1 \<sqinter> s2 = \<bottom>; sr_uniq (s1,r) a; sr_uniq (s2,r) a\<rbrakk> \<Longrightarrow> 
  \<exists> x i j. sr_indx_fst_map (s1,r) a x = Some i \<and> sr_indx_fst_map (s2,r) a x = Some j"
  apply(simp add: sr_indx_fst_map sr_uniq_def)
  apply(auto)
  apply(rule_tac x=x in exI)
  apply(drule_tac x=x in spec)+
  by(simp add: sp_uniq_def,fold rexcerpt_def,auto simp add: rexcerpt)

text \<open>If \<open>sr_uniq sr a\<close> this implies that all elements in excerpt \<open>sr_some sr\<close> of \<open>a\<close>
must be pairwise different (distinct), otherwise they would be 
specified by the same parameter value and the element at the larger index could not be found. In other
words, the index-to-element map \<open>sp_elem_map\<close> is injective on \<open>sr_some sr\<close>.\<close>
lemma inj_sp_elem_map: 
 "sr_uniq sr a \<Longrightarrow> inj_map (sp_elem_map (sr_some sr) a)"
  apply(simp add: inj_map_def)
  apply(rule inj_onI)
  apply(auto simp add: sp_elem_map)
  apply(case_tac "iexcerpt (sr_some sr) a x",simp_all)
  apply(case_tac "iexcerpt (sr_some sr) a y",simp_all)
  by(auto simp add: sr_uniq_def sr_some_def iexcerpt_def rexcrp_def sp_uniq_def)

lemma inj_p_elem_map: 
 "r_uniq r a \<Longrightarrow> inj_map (p_elem_map (r_some r) a)"
  apply(simp add: r_uniq_def p_elem_map_def r_some_sr_some)
  by(simp add: inj_sp_elem_map)

text \<open>If \<open>sr_bijective sr a\<close> this implies that \<open>sr_indx_all_inv = sr_indx_fst_inv\<close>, because
if an index is mapped to a parameter value \<open>x\<close> then there is no other such index and the 
first index found is the only such index.\<close>

lemma sr_indx_all_inv_eq_fst_inv:
 "sr_bijective sr a \<Longrightarrow> sr_indx_all_inv sr a = sr_indx_fst_inv sr a"
  apply(clarsimp simp add: sr_bijective_def)
  apply(rule ext)
  apply(frule inj_sr_indx_fst_map)
  apply(case_tac "sr_indx_all_inv sr a x",simp)
  apply(simp add: sr_indx_all_inv_None_iff)
   apply(simp add: sr_indx_fst_inv_def,rule sym)
   apply(simp add: inv_map_None_iff inj_ran_def inj_map_is_inj_part)
   apply(simp add: ran_def)
  apply(rule)
   apply(simp add:  sr_uniq_def sp_uniq_def sr_indx_fst_map)
   apply(simp add: rexcerpt)
   apply(rule,rule) apply(drule LeastI_ex)
   apply(auto)

  apply(simp add: sr_indx_all_inv_Some_iff)
   apply(simp add: sr_indx_fst_inv_def,rule sym)
   apply(simp add: inv_map_Some_iff inj_dom_def inj_map_is_inj_part)
  apply(simp add: dom_def)
  apply(simp add: sr_indx_fst_map sr_uniq_def sp_uniq_def,fold rexcerpt_def,simp add: rexcerpt)
  apply(auto)
  apply(rule Least_equality,simp)
  apply(drule_tac x=aa in spec)
  apply(drule_tac x=x in spec)
  by(simp)

text \<open>
The following lemmas are experimental, it is not clear whether they are useful. 
\<close>

text \<open>
If \<open>sr_injective sr a\<close> and \<open>sr_indx_all_inv sr a\<close> is injective 
then \<open>sr_uniq sr a\<close> holds.
\<close>

lemma injective_implies_sr_uniq:
 "\<lbrakk>sr_injective sr a; inj_map(sr_indx_all_inv sr a)\<rbrakk> \<Longrightarrow> sr_uniq sr a"
  apply(simp add: inj_map_def sr_uniq_def sp_uniq_def)
  apply(simp add: inj_on_def)
  apply(simp add: dom_def)
  apply(simp add: sr_indx_all_inv_Some_iff)

  apply(simp add: rexcrp_def iexcerpt_def)
  apply(auto)
  apply(drule_tac x=i in spec) apply(auto)
  apply(drule_tac x=j in spec) apply(auto)

  apply(case_tac "sr_indx_all_inv sr a i")
   apply(simp add: sr_indx_all_inv_None_iff)
   apply(simp add: sr_indx_all_inv_Some_iff)
  apply(case_tac "sr_indx_all_inv sr a j")
   apply(simp add: sr_indx_all_inv_None_iff)
   apply(simp add: sr_indx_all_inv_Some_iff)

     apply(simp add: sr_injective_def)
  apply(simp add: rexcerpt)
  apply(frule_tac x=i in spec)
  apply(drule_tac x=j in spec)
  apply(drule_tac x=x in spec)
  apply(drule_tac x=x in spec)
  apply(drule mp) apply(rule) apply(assumption) apply(rule) apply(assumption,assumption)
  apply(drule mp) apply(rule) apply(assumption) apply(rule) apply(assumption,assumption)
  apply(drule_tac x=aa in spec)
  apply(drule_tac x=aaa in spec)
  by(simp)

lemma sr_uniq_implies_injective:
 "\<lbrakk>sr_injective sr a; sr_uniq sr a\<rbrakk> \<Longrightarrow> inj_map(sr_indx_all_inv sr a)"
  apply(simp add: inj_map_def dom_def inj_on_def)
  apply(auto)
   apply(simp add: sr_indx_all_inv_Some_iff)
  apply(simp add:sr_uniq_def sp_uniq_def rexcrp_def iexcerpt_def)
  apply(drule_tac x=y in spec)
  by(simp)

lemma injective_sr_uniq_iff:
 "\<lbrakk>sr_injective sr a\<rbrakk> \<Longrightarrow> inj_map(sr_indx_all_inv sr a) = sr_uniq sr a"
  apply(auto)
   apply(rule injective_implies_sr_uniq,simp_all)
  by(rule sr_uniq_implies_injective,simp_all)

text \<open>If \<open>sr_bijective sr a\<close> then searching for the parameter associated with entry \<open>i\<close> will 
find \<open>i\<close>.\<close>

lemma sr_indx_fst_map_comp_all_inv:
 "\<lbrakk>sr_bijective sr a; iexcerpt (sr_some sr) a i\<rbrakk> \<Longrightarrow>
  (sr_indx_fst_map sr a \<circ>\<^sub>m sr_indx_all_inv sr a) i = Some i"
  apply(simp add: sr_indx_all_inv_eq_fst_inv)
  apply(simp add: sr_indx_fst_inv_def)
  apply(simp add: m_inv_map_m)
  apply(rule restrict_in)
  apply(simp add: sr_bijective_def inj_map_is_inj_part inj_sr_indx_fst_map)
  apply(simp add: sr_some_def iexcerpt_def) apply(clarsimp)
  apply(rule_tac a=x in ranI)
  apply(rule sr_indx_fst_sr_uniq)
  by (simp_all add: rexcerpt_def iexcerpt_def)

end
