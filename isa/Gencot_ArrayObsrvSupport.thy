section \<open>Array Support\<close>

theory Gencot_ArrayObsrvSupport
  imports Gencot_ArrayBaseSupport
begin

subsection \<open>Basic Observation Functions\<close>

text \<open>
The basic observation function views arrays as maps from indexes to elements. Derived observations are defined
for inverse maps, and for sets and numbers of indexes and elements. All functions support reducing the
observation to an array excerpt which can be specified by indexes, by elements, or both.
\<close>

subsubsection \<open>Basic Observation as a Map\<close>

text \<open>
The most basic observation function returns a map from indexes to elements for an array excerpt. 
\<close>
definition sp_elem_map :: "(nat \<times> 'el \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> nat \<rightharpoonup> 'el"
  where "sp_elem_map sp a \<equiv> map_of (filter sp (enumerate 0 a))"

text \<open>
Simplified forms where the excerpt is determined by index or element value alone or is the whole array.
\<close>
definition s_elem_map :: "(nat \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> nat \<rightharpoonup> 'el"
  where "s_elem_map s \<equiv> sp_elem_map (s\<circ>fst)"
definition p_elem_map :: "('el \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> nat \<rightharpoonup> 'el"
  where "p_elem_map p \<equiv> sp_elem_map (p\<circ>snd)"
definition elem_map :: "'el list \<Rightarrow> nat \<rightharpoonup> 'el"
  where "elem_map \<equiv> sp_elem_map \<top>"

text \<open>
Alternative standalone definitions:
\<close>
lemma sp_elem_map: 
  "sp_elem_map sp a = (\<lambda>i. (if iexcerpt sp a i then Some (nth a i) else None))"
  apply(simp add: sp_elem_map_def iexcerpt_def enumerate_eq_zip)
  apply(rule ext)
  apply(simp add:  filter_eq_nths)
  apply(rule conjI,rule impI)
   apply(subst map_of_eq_Some_iff)
    apply (metis (no_types, lifting) distinct_nthsI distinct_upt length_map map_fst_zip map_nth nths_map)
   apply(simp add: set_nths)
   apply(rule_tac x = i in exI,simp)
   apply(subst map_of_eq_None_iff)
  apply(rule impI)
  apply(simp add: set_nths)
  by auto
lemma s_elem_map: 
  "s_elem_map s a = (\<lambda>i. (if iexcerpt (s\<circ>fst) a i then Some (nth a i) else None))"
  by(simp add: s_elem_map_def sp_elem_map)
lemma p_elem_map: 
  "p_elem_map p a = (\<lambda>i. (if iexcerpt (p\<circ>snd) a i then Some (nth a i) else None))"
  by(simp add: p_elem_map_def sp_elem_map)
lemma elem_map: 
  "elem_map a = (\<lambda>i. (if i < length a then Some (nth a i) else None))"
  by(simp add: elem_map_def iexcerpt_def sp_elem_map)

text \<open>
Function \<open>elem_map\<close> observes the complete array, it is injective and can be inverted.
\<close>
definition elem_map_arr :: "(nat \<rightharpoonup> 'el) \<Rightarrow> 'el list"
  where "elem_map_arr m \<equiv> (map (the \<circ> m) [0..< card (dom m)])"

lemma elem_map_inverse:
 "elem_map_arr (elem_map a) = a"
  apply(simp add: elem_map elem_map_arr_def dom_def)
  apply(rule nth_equalityI)
   by(simp_all)
lemma elem_map_injective:
 "elem_map a = elem_map b \<Longrightarrow> a = b"
  apply(drule arg_cong[where f = elem_map_arr])
  by(simp add: elem_map_inverse)

subsubsection \<open>Restricting Maps to Sub Excerpts\<close>

text \<open>
A map for a sub excerpt can be constructed by compositon with a restriction map. The restriction
map is a partial identity which is undefined for all values which are not in the sub excerpt.

Since the excerpts may also depend on the index, the composition must be performed on an extended
map which preserves the index in addition to the element value. Such a map is called an
``iemap'' here. For restricting a map it must be converted to an iemap, composed with one or
more restriction maps and finally converted back.

For an excerpt \<open>p\<close> which does not depend on the index value the corresponding restriction map
can be directly composed with the element map.
\<close>

definition make_iemap :: "(nat \<rightharpoonup> 'el) \<Rightarrow> (nat \<rightharpoonup> nat \<times> 'el)"
  where "make_iemap = prsvarg_map"
definition from_iemap :: "(nat \<times> 'el \<rightharpoonup> 'el)"
  where "from_iemap = Some \<circ> snd"

definition sp_restrict_iemap :: "(nat \<times> 'el \<Rightarrow> bool) \<Rightarrow> (nat \<times> 'el \<rightharpoonup> nat \<times> 'el)"
  where "sp_restrict_iemap sp = (Some |` Collect sp)"
definition s_restrict_iemap :: "(nat \<Rightarrow> bool) \<Rightarrow> (nat \<times> 'el \<rightharpoonup> nat \<times> 'el)"
  where "s_restrict_iemap s = sp_restrict_iemap (s\<circ>fst)"
definition p_restrict_iemap :: "('el \<Rightarrow> bool) \<Rightarrow> (nat \<times> 'el \<rightharpoonup> nat \<times> 'el)"
  where "p_restrict_iemap p = sp_restrict_iemap (p\<circ>snd)"
definition p_restrict_map :: "('el \<Rightarrow> bool) \<Rightarrow> ('el \<rightharpoonup> 'el)"
  where "p_restrict_map p = (Some |` Collect p)"

lemma make_iemap:
 "make_iemap m = (\<lambda>x. case m x of None \<Rightarrow> None | Some y \<Rightarrow> Some (x,y))"
  by(simp add: make_iemap_def prsvarg_map)

lemma sp_elem_map_SP_le:
 "sp1 \<le> sp2 \<Longrightarrow> 
  sp_elem_map sp1 a = from_iemap \<circ>\<^sub>m sp_restrict_iemap sp1 \<circ>\<^sub>m (make_iemap (sp_elem_map sp2 a))"
  apply(simp add: from_iemap_def sp_restrict_iemap_def make_iemap)
  apply(simp add: sp_elem_map iexcerpt_def map_comp_def)
  apply(rule ext)
  by(auto)
lemma s_elem_map_S_le:
 "s1 \<le> s2 \<Longrightarrow> 
  s_elem_map s1 a = from_iemap \<circ>\<^sub>m s_restrict_iemap s1 \<circ>\<^sub>m (make_iemap (s_elem_map s2 a))"
  apply(simp add: s_restrict_iemap_def s_elem_map_def)
  by(rule sp_elem_map_SP_le,auto)
lemma p_elem_map_P_le:
 "p1 \<le> p2 \<Longrightarrow> 
  p_elem_map p1 a = from_iemap \<circ>\<^sub>m p_restrict_iemap p1 \<circ>\<^sub>m (make_iemap (p_elem_map p2 a))"
  apply(simp add: p_restrict_iemap_def p_elem_map_def)
  by(rule sp_elem_map_SP_le,auto)
lemma p_elem_map_P_le':
 "p1 \<le> p2 \<Longrightarrow> 
  p_elem_map p1 a = p_restrict_map p1 \<circ>\<^sub>m (p_elem_map p2 a)"
  apply(simp add: p_restrict_map_def p_elem_map iexcerpt_def map_comp_def)
  by(rule ext,auto)

text \<open>
Cases for mixed excerpt kinds. 
\<close>

lemma sp_elem_map_S_le:
 "sp \<le> (s\<circ>fst) \<Longrightarrow> 
  sp_elem_map sp a = from_iemap \<circ>\<^sub>m sp_restrict_iemap sp \<circ>\<^sub>m (make_iemap (s_elem_map s a))"
  by(simp add: s_elem_map_def sp_elem_map_SP_le)
lemma sp_elem_map_P_le:
 "sp \<le> (p\<circ>snd) \<Longrightarrow> 
  sp_elem_map sp a = from_iemap \<circ>\<^sub>m sp_restrict_iemap sp \<circ>\<^sub>m (make_iemap (p_elem_map p a))"
  by(simp add: p_elem_map_def sp_elem_map_SP_le)
lemma sp_elem_map_le:
 "sp_elem_map sp a = from_iemap \<circ>\<^sub>m sp_restrict_iemap sp \<circ>\<^sub>m (make_iemap (elem_map a))"
  by(simp add: elem_map_def sp_elem_map_SP_le)
lemma s_elem_map_le:
 "s_elem_map s a = from_iemap \<circ>\<^sub>m s_restrict_iemap s \<circ>\<^sub>m (make_iemap (elem_map a))"
  by(simp add: elem_map_def s_elem_map_def s_restrict_iemap_def sp_elem_map_SP_le)
lemma p_elem_map_le:
 "p_elem_map p a = from_iemap \<circ>\<^sub>m p_restrict_iemap p \<circ>\<^sub>m (make_iemap (elem_map a))"
  by(simp add: elem_map_def p_elem_map_def p_restrict_iemap_def sp_elem_map_SP_le)
lemma p_elem_map_le':
 "p_elem_map p a = p_restrict_map p \<circ>\<^sub>m (elem_map a)"
  apply(simp add: p_restrict_map_def p_elem_map elem_map iexcerpt_def map_comp_def)
  by(rule ext,auto)

text \<open>
If maps for an excerpt are equal on two arrays, they are equal for every sub excerpt.
\<close>

lemma sp_elem_map_SP_le_cong: 
 "sp1 \<le> sp2 \<Longrightarrow> sp_elem_map sp2 a = sp_elem_map sp2 b \<Longrightarrow>
  sp_elem_map sp1 a = sp_elem_map sp1 b"
  by(simp add: sp_elem_map_SP_le)
lemma s_elem_map_S_le_cong: 
 "s1 \<le> s2 \<Longrightarrow> s_elem_map s2 a = s_elem_map s2 b \<Longrightarrow>
  s_elem_map s1 a = s_elem_map s1 b"
  by(simp add: s_elem_map_S_le)
lemma p_elem_map_P_le_cong: 
 "p1 \<le> p2 \<Longrightarrow> p_elem_map p2 a = p_elem_map p2 b \<Longrightarrow>
  p_elem_map p1 a = p_elem_map p1 b"
  by(simp add: p_elem_map_P_le)

subsubsection \<open>Other Rules for the Maps\<close>

text \<open>
The map for a union of excerpts can be constructed by adding the maps for the excerpts.
\<close>
lemma sp_elem_map_SP_union:
 "sp_elem_map (sp1 \<squnion> sp2) a = (sp_elem_map sp1 a) ++ (sp_elem_map sp2 a)"
  by(auto simp add: sp_elem_map iexcerpt_def map_add_def)
lemma s_elem_map_S_union:
 "s_elem_map (s1 \<squnion> s2) a = (s_elem_map s1 a) ++ (s_elem_map s2 a)"
  by(auto simp add: s_elem_map iexcerpt_def map_add_def)
lemma p_elem_map_P_union:
 "p_elem_map (p1 \<squnion> p2) a = (p_elem_map p1 a) ++ (p_elem_map p2 a)"
  by(auto simp add: p_elem_map iexcerpt_def map_add_def)

text \<open>
The map for the empty excerpt is the empty map.
\<close>
lemma sp_elem_map_SP_bot:
 "sp_elem_map \<bottom> a = Map.empty"
  by(simp add: sp_elem_map iexcerpt_def)
lemma s_elem_map_S_bot:
 "s_elem_map \<bottom> a = Map.empty"
  by(simp add: s_elem_map iexcerpt_def)
lemma p_elem_map_P_bot:
 "p_elem_map \<bottom> a = Map.empty"
  by(simp add: p_elem_map iexcerpt_def)

text \<open>
The maps are monotonic with respect to the excerpts.
\<close>
lemma sp_elem_map_mono:
 "sp1 \<le> sp2 \<Longrightarrow> sp_elem_map sp1 a \<subseteq>\<^sub>m sp_elem_map sp2 a"
  by(auto simp add: sp_elem_map iexcerpt_def map_le_def dom_def)
lemma s_elem_map_mono:
 "s1 \<le> s2 \<Longrightarrow> s_elem_map s1 a \<subseteq>\<^sub>m s_elem_map s2 a"
  by(unfold s_elem_map_def,rule sp_elem_map_mono,auto)
lemma p_elem_map_mono:
 "p1 \<le> p2 \<Longrightarrow> p_elem_map p1 a \<subseteq>\<^sub>m p_elem_map p2 a"
  by(unfold p_elem_map_def,rule sp_elem_map_mono,auto)

text \<open>
If an excerpt covers all indices or all elements it can be simplified. 
\<close>
lemma sp_to_s_elem_map:
 "\<forall>i<length a. sp (i,nth a i) = s i \<Longrightarrow> sp_elem_map sp a = s_elem_map s a"
  apply(rule ext)
  by(auto simp add: s_elem_map_def sp_elem_map iexcerpt_def)
lemma sp_to_p_elem_map:
 "\<forall>i<length a. sp (i,nth a i) = p (nth a i) \<Longrightarrow> sp_elem_map sp a = p_elem_map p a"
  apply(rule ext)
  by(auto simp add: p_elem_map_def sp_elem_map iexcerpt_def)
lemma s_to_elem_map:
 "\<forall>i<length a. s i \<Longrightarrow> s_elem_map s a = elem_map a"
  apply(rule ext)
  by(simp add: elem_map_def s_elem_map iexcerpt_def sp_elem_map)
lemma p_to_elem_map:
 "\<forall>i<length a. p (nth a i) \<Longrightarrow> p_elem_map p a = elem_map a"
  apply(rule ext)
  by(simp add: elem_map_def p_elem_map iexcerpt_def sp_elem_map)

text \<open>
In the excerpt the map values for the excerpt map and the whole map are the same.
\<close>
lemma sp_eq_elem_map:
 "iexcerpt sp a i \<Longrightarrow> sp_elem_map sp a i = elem_map a i"
  by(simp add: sp_elem_map elem_map iexcerpt_def)
lemma s_eq_elem_map:
 "iexcerpt (s\<circ>fst) a i \<Longrightarrow> s_elem_map s a i = elem_map a i"
  by(simp add: s_elem_map elem_map iexcerpt_def)
lemma p_eq_elem_map:
 "iexcerpt (p\<circ>snd) a i \<Longrightarrow> p_elem_map p a i = elem_map a i"
  by(simp add: p_elem_map elem_map iexcerpt_def)

subsubsection \<open>The Ordered List of Elements for a Map\<close>

definition elem_lst_upto :: "nat \<Rightarrow> (nat \<rightharpoonup> 'el) \<Rightarrow> 'el list"
  where "elem_lst_upto n m \<equiv> map the (filter (\<lambda>x. x \<noteq> None) (map m [0..<n]))"

(* These are not trivial to prove:
lemma 
 "elem_lst_upto (length a) (sp_elem_map sp a) = 
  (map snd (filter sp (enumerate 0 a)))"
  apply(simp add: elem_lst_upto_def sp_elem_map_def)
  sorry
lemma 
 "elem_lst_upto (length a) (p_elem_map p a) = 
  (filter p a)"
  apply(simp add: elem_lst_upto_def p_elem_map iexcerpt_def)
  sorry
lemma
 "elem_lst_upto (length a) (s_elem_map s a) =
  nths a {i. i < length a \<and> s i}"
  apply(simp add: elem_lst_upto_def s_elem_map iexcerpt_def)
  sorry
lemma
 "elem_lst_upto (length a) (s_elem_map (iprefx i) a) =
  take i a"
  sorry
*)

lemma elem_lst_upto_elem_map:
 "elem_lst_upto (length a) (elem_map a) = a"
  apply(simp add: elem_lst_upto_def elem_map)
  by(rule nth_equalityI,simp_all)

text \<open>
Observation of some list functions and predicates.
\<close>

lemma sp_elem_map_take:
 "sp_elem_map sp (take i a) = sp_elem_map (sp \<sqinter> (iprefx i \<circ> fst)) a"
  apply(rule ext)
  by(clarsimp simp add: sp_elem_map iexcerpt_def iprefx)

lemma sp_elem_map_zip:
 "sp = (\<lambda>(i,(e1,e2)). sp1 (i,e1) \<and> sp2 (i,e2)) \<Longrightarrow>
  sp_elem_map sp (zip a1 a2) = map_split_map (sp_elem_map sp1 a1) (sp_elem_map sp2 a2)"
  apply(rule ext)
  apply(simp add: map_split_map_def dbl_arg_def map_prod_map_def times_option_def)
  by(simp add: sp_elem_map iexcerpt_def)

lemma sp_elem_map_map:
 "sp' = (\<lambda>(i,e). sp (i,f e)) ==> 
  sp_elem_map sp (map f a) = (Some \<circ> f) \<circ>\<^sub>m (sp_elem_map sp' a)"
  apply(rule ext)
  by(simp add: map_comp_def sp_elem_map iexcerpt_def)

subsection \<open>Derived Observation Functions\<close>

text \<open>
Derived observation functions are defined based on \<open>sp_elem_map\<close>. 
The functions are the inverse map, domain and range sets and their cardinalities. 
\<close>

definition sp_indx_map :: "(nat \<times> 'el \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> 'el \<rightharpoonup> nat"
  where "sp_indx_map sp a = inv_map (sp_elem_map sp a)"
definition sp_indx_set :: "(nat \<times> 'el \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> nat set"
  where "sp_indx_set sp a = dom (sp_elem_map sp a)"
definition sp_elem_set :: "(nat \<times> 'el \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> 'el set"
  where "sp_elem_set sp a = ran (sp_elem_map sp a)"
definition sp_indx_num :: "(nat \<times> 'el \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> nat"
  where "sp_indx_num sp a = card (sp_indx_set sp a)"
definition sp_elem_num :: "(nat \<times> 'el \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> nat"
  where "sp_elem_num sp a = card (sp_elem_set sp a)"

text \<open>
Alternative standalone definitions:
\<close>
(*
lemma sp_indx_map: 
 "sp_indx_map sp a = (\<lambda>e. (if \<exists>! i. iexcerpt sp a i \<and> e = (nth a i) then Some i else None))"
  sorry
*)
lemma sp_indx_set:
 "sp_indx_set sp a = {i. iexcerpt sp a i }"
  by(simp add: sp_indx_set_def sp_elem_map dom_def)
lemma sp_elem_set:
 "sp_elem_set sp a = {e. (\<exists> i. iexcerpt sp a i \<and> e = (nth a i)) }"
  by(auto simp add: sp_elem_set_def sp_elem_map ran_def)
lemma sp_indx_num:
 "sp_indx_num sp a = card {i. iexcerpt sp a i }"
  by(simp add: sp_indx_num_def sp_indx_set)
lemma sp_elem_num:
 "sp_elem_num sp a = card {e. (\<exists> i. iexcerpt sp a i \<and> e = (nth a i)) }"
  by(simp add: sp_elem_num_def sp_elem_set)

text \<open>
Simplified forms where the excerpt is determined by index or element value alone or is the whole array.
\<close>
definition s_indx_map :: "(nat \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> 'el \<rightharpoonup> nat"
  where "s_indx_map s = sp_indx_map (s\<circ>fst)"
definition s_indx_set :: "(nat \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> nat set"
  where "s_indx_set s = sp_indx_set (s\<circ>fst)"
definition s_elem_set :: "(nat \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> 'el set"
  where "s_elem_set s = sp_elem_set (s\<circ>fst)"
definition s_indx_num :: "(nat \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> nat"
  where "s_indx_num s = sp_indx_num (s\<circ>fst)"
definition s_elem_num :: "(nat \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> nat"
  where "s_elem_num s = sp_elem_num (s\<circ>fst)"

definition p_indx_map :: "('el \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> 'el \<rightharpoonup> nat"
  where "p_indx_map p = sp_indx_map (p\<circ>snd)"
definition p_indx_set :: "('el \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> nat set"
  where "p_indx_set p = sp_indx_set (p\<circ>snd)"
definition p_elem_set :: "('el \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> 'el set"
  where "p_elem_set p = sp_elem_set (p\<circ>snd)"
definition p_indx_num :: "('el \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> nat"
  where "p_indx_num p = sp_indx_num (p\<circ>snd)"
definition p_elem_num :: "('el \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> nat"
  where "p_elem_num p = sp_elem_num (p\<circ>snd)"

definition indx_map :: "'el list \<Rightarrow> 'el \<rightharpoonup> nat"
  where "indx_map = sp_indx_map \<top>"
definition indx_set :: "'el list \<Rightarrow> nat set"
  where "indx_set = sp_indx_set \<top>"
definition elem_set :: "'el list \<Rightarrow> 'el set"
  where "elem_set = sp_elem_set \<top>"
definition indx_num :: "'el list \<Rightarrow> nat"
  where "indx_num = sp_indx_num \<top>"
definition elem_num :: "'el list \<Rightarrow> nat"
  where "elem_num = sp_elem_num \<top>"

text \<open>
Alternative standalone definitions:
\<close>
(*
lemma s_indx_map: 
 "s_indx_map s a = (\<lambda>e. (if \<exists>! i. vld a i \<and> s i \<and> e = (nth a i) then Some i else None))"
  sorry
*)
lemma s_indx_set:
 "s_indx_set s a = {i. vld a i \<and> s i}"
  by(simp add: s_indx_set_def sp_indx_set iexcerpt_def)
lemma s_elem_set:
 "s_elem_set s a = {e. (\<exists> i. vld a i \<and> s i \<and> e = (nth a i)) }"
  by(auto simp add: s_elem_set_def sp_elem_set iexcerpt_def)
lemma s_indx_num:
 "s_indx_num s a = card {i. vld a i \<and> s i }"
  by(simp add: s_indx_num_def sp_indx_num iexcerpt_def)
lemma s_elem_num:
 "s_elem_num s a = card {e. (\<exists> i. vld a i \<and> s i \<and> e = (nth a i)) }"
  by(simp add: s_elem_num_def sp_elem_num iexcerpt_def)

(*
lemma p_indx_map: 
 "p_indx_map p a = (\<lambda>e. (if \<exists>! i. vld a i \<and> e = (nth a i)\<and> p e then Some i else None))"
  sorry
*)
lemma p_indx_set:
 "p_indx_set p a = {i. vld a i \<and> p (nth a i) }"
  by(simp add: p_indx_set_def sp_indx_set iexcerpt_def)
lemma p_elem_set:
 "p_elem_set p a = {e. (\<exists> i. vld a i \<and> e = (nth a i) \<and> p e) }"
  by(auto simp add: p_elem_set_def sp_elem_set iexcerpt_def)
lemma p_indx_num:
 "p_indx_num p a = card {i. vld a i \<and> p (nth a i) }"
  by(simp add: p_indx_num_def sp_indx_num iexcerpt_def)
lemma p_elem_num:
 "p_elem_num p a = card {e. (\<exists> i. vld a i \<and> e = (nth a i) \<and> p e) }"
  by(simp add: p_elem_num_def sp_elem_num iexcerpt_def,metis)

(*
lemma indx_map: 
 "indx_map a = (\<lambda>e. (if \<exists>! i. vld a i \<and> e = (nth a i) then Some i else None))"
  sorry
*)
lemma indx_set:
 "indx_set a = {i. vld a i }"
  by(simp add: indx_set_def sp_indx_set iexcerpt_def)
lemma elem_set:
 "elem_set a = {e. (\<exists> i. vld a i \<and> e = (nth a i)) }"
  by(auto simp add: elem_set_def sp_elem_set iexcerpt_def)
lemma indx_num:
 "indx_num a = length a"
  by(simp add: indx_num_def sp_indx_num iexcerpt_def)
lemma elem_num:
 "elem_num a = card {e. (\<exists> i. vld a i \<and> e = (nth a i)) }"
  by(simp add: elem_num_def sp_elem_num iexcerpt_def)

text \<open>
The domain and range sets are always finite.
\<close>
lemma sp_indx_set_finite[simp]:
 "finite (dom (sp_elem_map sp a))"
  by(fold sp_indx_set_def, simp add: sp_indx_set iexcerpt_def)
lemma sp_elem_set_finite[simp]:
 "finite (ran (sp_elem_map sp a))"
  by(fold sp_elem_set_def, simp add: sp_elem_set iexcerpt_def)
lemma s_indx_set_finite[simp]:
 "finite (dom (s_elem_map s a))"
  by(simp add: s_elem_map_def s_indx_set iexcerpt_def)
lemma s_elem_set_finite[simp]:
 "finite (ran (s_elem_map s a))"
  by(simp add: s_elem_map_def s_elem_set iexcerpt_def)
lemma p_indx_set_finite[simp]:
 "finite (dom (p_elem_map p a))"
  by(simp add: p_elem_map_def p_indx_set iexcerpt_def)
lemma p_elem_set_finite[simp]:
 "finite (ran (p_elem_map p a))"
  by(simp add: p_elem_map_def p_elem_set iexcerpt_def)
lemma indx_set_finite[simp]:
 "finite (dom (elem_map a))"
  by(simp add: elem_map_def indx_set iexcerpt_def)
lemma elem_set_finite[simp]:
 "finite (ran (elem_map a))"
  by(simp add: elem_map_def elem_set iexcerpt_def)

text \<open>
The maps are injective iff the number of elements equals the number of indexes.
\<close>
lemma sp_elem_map_injective_iff:
 "inj_map (sp_elem_map sp a) = (sp_indx_num sp a = sp_elem_num sp a)"
  apply(simp add: inj_map_iff)
  by(auto simp add: sp_indx_num_def sp_indx_set_def sp_elem_num_def sp_elem_set_def)
lemma s_elem_map_injective_iff:
 "inj_map (s_elem_map s a) = (s_indx_num s a = s_elem_num s a)"
  by(simp add: s_elem_map_def s_indx_num_def s_elem_num_def sp_elem_map_injective_iff)
lemma p_elem_map_injective_iff:
 "inj_map (p_elem_map p a) = (p_indx_num p a = p_elem_num p a)"
  by(simp add: p_elem_map_def p_indx_num_def p_elem_num_def sp_elem_map_injective_iff)
lemma elem_map_injective_iff:
 "inj_map (elem_map a) = (indx_num a = elem_num a)"
  by(simp add: elem_map_def indx_num_def elem_num_def sp_elem_map_injective_iff)

text \<open>
The map \<open>elem_map a\<close> is injective iff list \<open>a\<close> is distinct.
\<close>
lemma elem_map_inj_map_iff_distinct:
 "inj_map (elem_map a) = distinct a"
  apply(simp add: distinct_conv_nth)
  apply(simp add: elem_map inj_map_def dom_def inj_on_def)
  by(auto)

text \<open>
Observations for a union of excerpts.
\<close>

(* 
lemma sp_indx_map_SP_union: todo
lemma s_indx_map_S_union: todo
lemma p_indx_map_P_union: todo
*)

lemma sp_indx_set_SP_union:
 "sp_indx_set (sp1 \<squnion> sp2) a = (sp_indx_set sp1 a) \<union> (sp_indx_set sp2 a)"
  by(auto simp add: sp_indx_set_def sp_elem_map_SP_union)
lemma s_indx_set_S_union:
 "s_indx_set (s1 \<squnion> s2) a = (s_indx_set s1 a) \<union> (s_indx_set s2 a)"
  by(simp add: s_indx_set_def un_comp_pred sp_indx_set_SP_union)
lemma p_indx_set_P_union:
 "p_indx_set (p1 \<squnion> p2) a = (p_indx_set p1 a) \<union> (p_indx_set p2 a)"
  by(simp add: p_indx_set_def un_comp_pred sp_indx_set_SP_union)

lemma sp_elem_set_SP_union:
 "sp1 \<sqinter> sp2 = \<bottom> \<Longrightarrow> 
  sp_elem_set (sp1 \<squnion> sp2) a = (sp_elem_set sp1 a) \<union> (sp_elem_set sp2 a)"
  apply(simp add: sp_elem_set_def sp_elem_map_SP_union)
  apply(rule ran_map_add)
  apply(auto simp add: sp_elem_map iexcerpt_def dom_def Collect_conj_eq[symmetric])
  by(drule_tac x="(x, a ! x)" in disjoint_pred,auto)
lemma s_elem_set_S_union:
 "s_elem_set (s1 \<squnion> s2) a = (s_elem_set s1 a) \<union> (s_elem_set s2 a)"
  apply(simp add: s_elem_set)
  by(auto simp add: Collect_disj_eq[symmetric])
lemma p_elem_set_P_union:
 "p_elem_set (p1 \<squnion> p2) a = (p_elem_set p1 a) \<union> (p_elem_set p2 a)"
  apply(simp add: p_elem_set)
  by(auto simp add: Collect_disj_eq[symmetric])

lemma sp_indx_num_SP_union:
 "sp1 \<sqinter> sp2 = \<bottom> \<Longrightarrow> 
  sp_indx_num (sp1 \<squnion> sp2) a = (sp_indx_num sp1 a) + (sp_indx_num sp2 a)"
  apply(simp add: sp_indx_num_def sp_indx_set_SP_union)
  apply(simp add: sp_indx_set iexcerpt_def)
  apply(rule card_Un_disjoint,auto)
  by(drule_tac x="(x, a ! x)" in disjoint_pred,auto)
lemma s_indx_num_S_union:
 "s1 \<sqinter> s2 = \<bottom> \<Longrightarrow> 
  s_indx_num (s1 \<squnion> s2) a = (s_indx_num s1 a) + (s_indx_num s2 a)"
  apply(simp add: s_indx_num_def un_comp_pred)
  apply(rule sp_indx_num_SP_union)
  using disjoint_pred by fastforce
lemma p_indx_num_P_union:
 "p1 \<sqinter> p2 = \<bottom> \<Longrightarrow> 
  p_indx_num (p1 \<squnion> p2) a = (p_indx_num p1 a) + (p_indx_num p2 a)"
  apply(simp add: p_indx_num_def un_comp_pred)
  apply(rule sp_indx_num_SP_union)
  using disjoint_pred by fastforce

lemma sp_elem_num_SP_union:
 "sp1 \<sqinter> sp2 = \<bottom> \<and> (sp_elem_set sp1 a) \<inter> (sp_elem_set sp2 a) = {} \<Longrightarrow> 
  sp_elem_num (sp1 \<squnion> sp2) a = (sp_elem_num sp1 a) + (sp_elem_num sp2 a)"
  apply(simp add: sp_elem_num_def sp_elem_set_SP_union)
  apply(rule card_Un_disjoint,auto)
  by(auto simp add: sp_elem_set iexcerpt_def)
lemma s_elem_num_S_union:
 "(s_elem_set s1 a) \<inter> (s_elem_set s2 a) = {} \<Longrightarrow> 
  s_elem_num (s1 \<squnion> s2) a = (s_elem_num s1 a) + (s_elem_num s2 a)"
  apply(simp add: s_elem_num)
  apply(subst card_Un_disjoint[symmetric],simp_all add: s_elem_set)
  apply(auto simp add: Collect_disj_eq[symmetric])
  by(rule_tac f=card in arg_cong,auto)
lemma p_elem_num_P_union:
 "(p_elem_set p1 a) \<inter> (p_elem_set p2 a) = {} \<Longrightarrow> 
  p_elem_num (p1 \<squnion> p2) a = (p_elem_num p1 a) + (p_elem_num p2 a)"
  apply(simp add: p_elem_num)
  apply(subst card_Un_disjoint[symmetric],simp_all add: p_elem_set)
  apply(auto simp add: Collect_disj_eq[symmetric])
  by(rule_tac f=card in arg_cong,auto)

text \<open>
If an excerpt covers all indices or all elements observations can be simplified.
\<close>
(*
lemma sp_to_s_indx_map:
 "\<forall>i<length a. sp (i,nth a i) = s i \<Longrightarrow>
  sp_indx_map sp a = s_indx_map s a"
  apply(simp add: s_indx_map_def)
  apply(subst sp_indx_map)+
  apply(rule ext)
  by(auto simp add: iexcerpt_def)
*)
lemma sp_to_s_indx_set:
 "\<forall>i<length a. sp (i,nth a i) = s i \<Longrightarrow>
  sp_indx_set sp a = s_indx_set s a"
  apply(simp add: s_indx_set_def sp_indx_set iexcerpt_def)
  by(rule Collect_cong,auto)
lemma sp_to_s_elem_set:
 "\<forall>i<length a. sp (i,nth a i) = s i \<Longrightarrow>
  sp_elem_set sp a = s_elem_set s a"
  apply(simp add: s_elem_set_def sp_elem_set iexcerpt_def)
  by(rule Collect_cong,auto)
lemma sp_to_s_indx_num:
 "\<forall>i<length a. sp (i,nth a i) = s i \<Longrightarrow>
  sp_indx_num sp a = s_indx_num s a"
  apply(simp add: s_indx_num_def sp_indx_num iexcerpt_def)
  by(rule_tac f=card in arg_cong,auto)
lemma sp_to_s_elem_num:
 "\<forall>i<length a. sp (i,nth a i) = s i \<Longrightarrow>
  sp_elem_num sp a = s_elem_num s a"
  apply(simp add: s_elem_num_def sp_elem_num iexcerpt_def)
  by(rule_tac f=card in arg_cong,auto)

(*
lemma sp_to_p_indx_map:
 "\<forall>i<length a. sp (i,nth a i) = p (nth a i) \<Longrightarrow>
  sp_indx_map sp a = p_indx_map p a"
  apply(simp add: p_indx_map_def)
  apply(subst sp_indx_map)+
  apply(rule ext)
  by(auto simp add: iexcerpt_def)
*)
lemma sp_to_p_indx_set:
 "\<forall>i<length a. sp (i,nth a i) = p (nth a i) \<Longrightarrow>
  sp_indx_set sp a = p_indx_set p a"
  apply(simp add: p_indx_set_def sp_indx_set iexcerpt_def)
  by(rule Collect_cong,auto)
lemma sp_to_p_elem_set:
 "\<forall>i<length a. sp (i,nth a i) = p (nth a i) \<Longrightarrow>
  sp_elem_set sp a = p_elem_set p a"
  apply(simp add: p_elem_set_def sp_elem_set iexcerpt_def)
  by(rule Collect_cong,auto)
lemma sp_to_p_indx_num:
 "\<forall>i<length a. sp (i,nth a i) = p (nth a i) \<Longrightarrow>
  sp_indx_num sp a = p_indx_num p a"
  apply(simp add: p_indx_num_def sp_indx_num iexcerpt_def)
  by(rule_tac f=card in arg_cong,auto)
lemma sp_to_p_elem_num:
 "\<forall>i<length a. sp (i,nth a i) = p (nth a i) \<Longrightarrow>
  sp_elem_num sp a = p_elem_num p a"
  apply(simp add: p_elem_num_def sp_elem_num iexcerpt_def)
  by(rule_tac f=card in arg_cong,auto)

(*
lemma s_to_indx_map:
 "\<forall>i<length a. s i \<Longrightarrow>
  s_indx_map s a = indx_map a"
  apply(simp add: indx_map_def s_indx_map_def)
  apply(subst sp_indx_map)+
  apply(rule ext)
  by(auto simp add: iexcerpt_def)
*)
lemma s_to_indx_set:
 "\<forall>i<length a. s i \<Longrightarrow>
  s_indx_set s a = indx_set a"
  by(auto simp add: indx_set_def s_indx_set iexcerpt_def sp_indx_set)
lemma s_to_elem_set:
 "\<forall>i<length a. s i \<Longrightarrow>
  s_elem_set s a = elem_set a"
  by(auto simp add: elem_set_def s_elem_set iexcerpt_def sp_elem_set)
lemma s_to_indx_num:
 "\<forall>i<length a. s i \<Longrightarrow>
  s_indx_num s a = indx_num a"
  apply(auto simp add: indx_num_def s_indx_num iexcerpt_def sp_indx_num)
  apply(subst (2) card_Collect_less_nat[where n="length a",symmetric])
  by(rule_tac f=card in arg_cong,auto)
lemma s_to_elem_num:
 "\<forall>i<length a. s i \<Longrightarrow>
  s_elem_num s a = elem_num a"
  apply(auto simp add: elem_num_def s_elem_num iexcerpt_def sp_elem_num)
  by(rule_tac f=card in arg_cong,auto)

(*
lemma p_to_indx_map:
 "\<forall>i<length a. p (nth a i) \<Longrightarrow>
  p_indx_map p a = indx_map a"
  apply(simp add: indx_map_def p_indx_map_def)
  apply(subst sp_indx_map)+
  apply(rule ext)
  by(auto simp add: iexcerpt_def)
*)
lemma p_to_indx_set:
 "\<forall>i<length a. p (nth a i) \<Longrightarrow>
  p_indx_set p a = indx_set a"
  by(auto simp add: indx_set_def p_indx_set iexcerpt_def sp_indx_set)
lemma p_to_elem_set:
 "\<forall>i<length a. p (nth a i) \<Longrightarrow>
  p_elem_set p a = elem_set a"
  by(auto simp add: elem_set_def p_elem_set iexcerpt_def sp_elem_set)
lemma p_to_indx_num:
 "\<forall>i<length a. p (nth a i) \<Longrightarrow>
  p_indx_num p a = indx_num a"
  apply(auto simp add: indx_num_def p_indx_num iexcerpt_def sp_indx_num)
  apply(subst (2) card_Collect_less_nat[where n="length a",symmetric])
  by(rule_tac f=card in arg_cong,auto)
lemma p_to_elem_num:
 "\<forall>i<length a. p (nth a i) \<Longrightarrow>
  p_elem_num p a = elem_num a"
  apply(auto simp add: elem_num_def p_elem_num iexcerpt_def sp_elem_num)
  by(rule_tac f=card in arg_cong,auto)

end
