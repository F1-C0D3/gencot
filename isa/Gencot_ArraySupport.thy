section \<open>Array Support\<close>

theory Gencot_ArraySupport
  imports Gencot_MapSupport
  "HOL-Library.Adhoc_Overloading"
  Gencot_PartAccessSupport
begin

(* These notations are removed in Main.thy, reactivate them. *)
notation
  bot ("\<bottom>") and top ("\<top>") and
  inf (infixl "\<sqinter>" 70) and sup (infixl "\<squnion>" 65) and
  Inf ("\<Sqinter>") and Sup ("\<Squnion>")

definition comp_snd :: "('a \<times> 'b \<Rightarrow> 'c) \<Rightarrow> ('a \<times> 'd \<Rightarrow> 'b) \<Rightarrow> ('a \<times> 'd \<Rightarrow> 'c)" (infixl "\<circ>\<^sub>2" 55)
  where "f \<circ>\<^sub>2 g \<equiv> \<lambda>(x,y). f (x,g(x,y))"

lemma top_pred: "(\<lambda>a. True) = \<top>" by auto
lemma bot_pred: "(\<lambda>a. False) = \<bottom>" by auto
lemma disjoint_pred: "sp1 \<sqinter> sp2 = \<bottom> \<Longrightarrow> (sp1 x \<and> sp2 x) = False"
  by (metis (full_types) bot_pred inf.idem inf_apply)
lemma un_comp_pred: "sp1 \<squnion> sp2 \<circ> sp = (sp1 \<circ> sp) \<squnion> (sp2 \<circ> sp)" by auto
lemma disjoint_diff_pred: "sp1 \<sqinter> sp2 = \<bottom> \<Longrightarrow> (sp1 - sp2) = sp1" for sp1 :: "'a \<Rightarrow> bool"
  apply(rule ext)
  using disjoint_pred by fastforce
lemma neg_pred[simp]: "- p = (\<lambda>a. \<not> p a)"
  by auto
lemma minus_pred: "p1 - p2 = (\<lambda>a. p1 a \<and> \<not> p2 a)"
  by(auto)

text \<open>
This theory provides support for representing arrays from programming languages as lists. An array with
elements of a type \<open>'el\<close> is represented by lists of type \<open>'el list\<close>. The theory defines
observation and modification functions for modeling the use of arrays in programs and develop abstract
views on it. The main characteristics of the defined functions is that list elements are associated with an index
counted from \<open>0\<close> and that modification functions never modify the list length.
\<close>

subsection \<open>Array Excerpts\<close>

text \<open>
An array excerpt is specified by a predicate on pairs of index and element. One way of constructing 
such predicates is from a predicate \<open>s\<close> on index values and a separate predicate \<open>p\<close> on elements. They
are lifted to excerpts by \<open>s \<circ> fst\<close> and \<open>p \<circ> snd\<close>, their conjunction is constructed by \<open>pred_prod s p\<close>
We use the abbreviation \<open>sp\<close> for a general excerpt and the abbreviations \<open>s\<close> and \<open>p\<close> for an excerpt 
specified by indexes or elements alone.
\<close>

text \<open>
The following function converts an excerpt to a predicate on the indexes of an actual array represented as a list.
\<close>
definition iexcerpt :: "(nat \<times> 'el \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> nat \<Rightarrow> bool"
  where "iexcerpt sp a \<equiv> \<lambda>i. i < length a \<and> sp (i,nth a i)"

text \<open>
The following function is an abbreviation for testing whether an index is valid for an array.
\<close>

definition vld :: "'el list \<Rightarrow> nat \<Rightarrow> bool"
  where "vld \<equiv> iexcerpt \<top>"

lemma vld[simp]: "vld a i = (i < length a)"
  by(simp add: vld_def iexcerpt_def)

subsubsection \<open>Index based Excerpts\<close>

text \<open>
Specific predicates are defined for excerpts specified by indexes only:
\<close>
definition islice :: "nat \<times> nat \<Rightarrow> nat \<Rightarrow> bool"
  where "islice ii \<equiv> \<lambda>i. (fst ii) \<le> i \<and> i < (snd ii)"
definition iprefx :: "nat \<Rightarrow> nat \<Rightarrow> bool"
  where "iprefx \<equiv> (curry islice) 0"
definition isingl :: "nat \<Rightarrow> nat \<Rightarrow> bool"
  where "isingl i \<equiv> islice (i, Suc i)"

lemma iprefx: "iprefx im = (\<lambda>i. i < im)"
  by(simp add: iprefx_def islice_def)
lemma isingl: "isingl i0 = (\<lambda>i. i = i0)"
  by(auto simp add: isingl_def islice_def)

lemma islice_bot:
 "im \<le> i0 \<Longrightarrow> islice (i0, im) = \<bottom>"
  by(auto simp add: islice_def)
lemma iprefx_bot:
 "iprefx 0 = \<bottom>"
  by(simp add: iprefx_def islice_bot)

lemma islice_le:
 "i0 \<le> j0 \<and> im \<ge> jm \<Longrightarrow> islice (i0, im) \<ge> islice (j0, jm)"
  by(auto simp add: islice_def)
lemma iprefx_le:
 "im \<le> jm \<Longrightarrow> iprefx im \<le> iprefx jm"
  by(simp add: iprefx_def islice_le)

text \<open>
Union of index based excerpts:
\<close>
lemma islice_islice:
 "i0 \<le> im' \<and> im' \<le> im \<Longrightarrow> (islice (im', im)) \<squnion> (islice (i0, im')) = (islice (i0, im))"
  by(auto simp add: islice_def)
lemma isingl_islice:
 "i0 \<le> im \<Longrightarrow> (isingl im) \<squnion> (islice (i0, im)) = (islice (i0, Suc im))"
  by(simp add: isingl_def islice_islice)
lemma isingl_iprefx:
 "(isingl im) \<squnion> (iprefx im) = (iprefx (Suc im))"
  by(simp add: iprefx_def isingl_islice)

subsubsection \<open>Index based Excerpts with a predicate\<close>

text \<open>
The following functions combine the index based excerpts with an element predicate.
\<close>

definition pslice :: "(nat \<times> nat) \<times> ('el \<Rightarrow> bool) \<Rightarrow> nat \<times> 'el \<Rightarrow> bool"
  where "pslice iip \<equiv> pred_prod (islice (fst iip)) (snd iip)"
definition pprefx :: "nat \<times> ('el \<Rightarrow> bool) \<Rightarrow> nat \<times> 'el \<Rightarrow> bool"
  where "pprefx ip \<equiv> pred_prod (iprefx (fst ip)) (snd ip)"
definition psingl :: "nat \<times> ('el \<Rightarrow> bool) \<Rightarrow> nat \<times> 'el \<Rightarrow> bool"
  where "psingl ip \<equiv> pred_prod (isingl (fst ip)) (snd ip)"

lemma pprefx: "pprefx ip = (\<lambda>(i,e). i < (fst ip) \<and> (snd ip) e)"
  by(auto simp add: pprefx_def iprefx)
lemma psingl: "psingl ip = (\<lambda>(i,e). i = (fst ip) \<and> (snd ip) e )"
  by(auto simp add: psingl_def isingl)

lemma pslice_bot:
 "((snd\<circ>fst) iip) \<le> ((fst\<circ>fst) iip) \<Longrightarrow> pslice iip = \<bottom>"
  by(auto simp add: pslice_def islice_def)
lemma pprefx_bot:
 "pprefx (0, p) = \<bottom>"
  by(auto simp add: pprefx iprefx_bot)

lemma pslice_le:
 "(fst ii) \<le> (fst jj) \<and> (snd ii) \<ge> (snd jj) \<Longrightarrow> 
  pslice (ii,p) \<ge> pslice (jj,p)"
  by(auto simp add: pslice_def islice_def)
lemma pprefx_le:
 "i \<le> j \<Longrightarrow> pprefx (i, p) \<le> pprefx (j, p)"
  by(auto simp add: pprefx islice_def)

lemma psingl_pprefx:
 "(psingl (i, p)) \<squnion> (pprefx (i, p)) = (pprefx (Suc i, p))"
  by(auto simp add: pprefx psingl islice_def)


subsubsection \<open>Index based Excerpts with a Relation\<close>

text \<open>
The following functions combine the index based excerpts with a relation between
an additional parameter and an element. 
\<close>

definition rslice :: "(nat \<times> nat) \<times> ('t \<Rightarrow> 'el \<Rightarrow> bool) \<Rightarrow> 't \<Rightarrow> nat \<times> 'el \<Rightarrow> bool"
  where "rslice iir \<equiv> \<lambda>x. pred_prod (islice (fst iir)) (snd iir x)"
definition rprefx :: "nat \<times> ('t \<Rightarrow> 'el \<Rightarrow> bool) \<Rightarrow> 't \<Rightarrow> nat \<times> 'el \<Rightarrow> bool"
  where "rprefx ir \<equiv> \<lambda>x. pred_prod (iprefx (fst ir)) (snd ir x)"
definition rsingl :: "nat \<times> ('t \<Rightarrow> 'el \<Rightarrow> bool) \<Rightarrow> 't \<Rightarrow> nat \<times> 'el \<Rightarrow> bool"
  where "rsingl ir \<equiv> \<lambda>x. pred_prod (isingl (fst ir)) (snd ir x)"

lemma rprefx: "rprefx ir = (\<lambda>x (i,e). i < (fst ir) \<and> snd ir x e)"
  apply(auto simp add: rprefx_def iprefx)
  by(rule ext,auto)
lemma rsingl: "rsingl ir = (\<lambda>x (i,e). i = (fst ir) \<and> snd ir x e)"
  apply(auto simp add: rsingl_def isingl)
  by(rule ext,auto)

lemma rprefx_pprefx: "rprefx (i,r) x = pprefx (i, r x)"
  by(simp add: rprefx_def pprefx_def)
lemma rsingl_psingl: "rsingl (i,r) x = psingl (i, r x)"
  by(simp add: rsingl_def psingl_def)

lemma rslice_bot:
 "((snd\<circ>fst) iir) \<le> ((fst\<circ>fst) iir) \<Longrightarrow> rslice iir = \<bottom>"
  apply(auto simp add: rslice_def islice_def)
  by(rule ext,auto)
lemma rprefx_bot:
 "rprefx (0, r) = \<bottom>"
  by(auto simp add: rprefx iprefx_bot)

lemma rslice_le:
 "(fst ii) \<le> (fst jj) \<and> (snd ii) \<ge> (snd jj) \<Longrightarrow> 
  rslice (ii,r) \<ge> rslice (jj,r)"
  by(auto simp add: rslice_def islice_def)
lemma rprefx_le:
 "i \<le> j \<Longrightarrow> rprefx (i, r) \<le> rprefx (j, r)"
  by(auto simp add: rprefx islice_def)

lemma rsingl_rprefx:
 "(rsingl (i, r)) \<squnion> (rprefx (i, r)) = (rprefx (Suc i, r))"
  apply(auto simp add: rprefx rsingl islice_def)
  by(rule ext,auto)

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
If the search excerpt predicate \<open>sp\<close> depends on a parameter, the search may return an index
or element for every parameter value. This is equivalent to a map from parameter values to
index or element values. The search excerpt predicate is equivalent to a relation \<open>sr\<close>
between parameter values and excerpts. The following functions are derived observations 
for observing maps resulting from such excerpt relations.
\<close>

definition sr_indx_fst_map :: "('t \<Rightarrow> nat \<times> 'el \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> 't \<rightharpoonup> nat"
  where "sr_indx_fst_map sr a \<equiv> \<lambda>x. sp_indx_fst (sr x) a"
definition sr_elem_fst_map :: "('t \<Rightarrow> nat \<times> 'el \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> 't \<rightharpoonup> 'el"
  where "sr_elem_fst_map sr a \<equiv> \<lambda>x. sp_elem_fst (sr x) a"

text \<open>
Simplified forms where the excerpt is determined by element value alone.
\<close>
definition r_indx_fst_map :: "('t \<Rightarrow> 'el \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> 't \<rightharpoonup> nat"
  where "r_indx_fst_map r \<equiv> sr_indx_fst_map (\<lambda>x.(r x)\<circ>snd)"
definition r_elem_fst_map :: "('t \<Rightarrow> 'el \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> 't \<rightharpoonup> 'el"
  where "r_elem_fst_map r \<equiv> sr_elem_fst_map (\<lambda>x.(r x)\<circ>snd)"

text \<open>
Alternative standalone definitions:
\<close>
lemma sr_indx_fst_map:
 "sr_indx_fst_map sr a = 
  (\<lambda>x. if \<forall>i. \<not> (iexcerpt (sr x) a i) then None else Some (LEAST i. (iexcerpt (sr x) a i)))"
  by(simp add: sr_indx_fst_map_def sp_indx_fst)

lemma sr_elem_fst_map:
 "sr_elem_fst_map sr a = 
  (\<lambda>x. if \<forall>i. \<not> (iexcerpt (sr x) a i) then None else Some (nth a (LEAST i. (iexcerpt (sr x) a i))))"
  by(simp add: sr_elem_fst_map_def sp_elem_fst)

lemma r_indx_fst_map:
 "r_indx_fst_map r a = 
  (\<lambda>x. if \<forall>i. vld a i \<longrightarrow> \<not> r x (a!i) then None else Some (LEAST i. vld a i \<and> r x (a!i)))"
  apply(unfold r_indx_fst_map_def)
  apply(simp add: sr_indx_fst_map)
  by(rule ext, simp add: iexcerpt_def)

lemma r_elem_fst_map:
 "r_elem_fst_map r a = 
  (\<lambda>x. if \<forall>i. vld a i \<longrightarrow> \<not> r x (a!i) then None else Some (a ! (LEAST i. vld a i \<and> r x (a!i))))"
  apply(unfold r_elem_fst_map_def)
  by(auto simp add: sr_elem_fst_map iexcerpt_def)

text \<open>
Function \<open>sr_elem_fst_map\<close> is mainly equivalent to the composition of
\<open>sr_indx_fst_map\<close> and \<open>sp_elem_map\<close>. In this composition \<open>sp_elem_map\<close> can
be reduced to the excerpt where \<open>sr\<close> is satisfied for some parameter value. This is 
expressed by defining a function \<open>sr_some\<close> which transforms the relation \<open>sr\<close> to a 
corresponding predicate \<open>sp\<close> which can be used as excerpt predicate. 

Since \<open>sr_indx_fst_map\<close> returns only valid indexes where the element satisfies
the relation \<open>sr\<close> for some parameter value the composition does not restrict the maps
and \<open>elem_map\<close> can be used instead of \<open>sp_elem_map\<close>.
\<close>

definition sr_some :: "('t \<Rightarrow> (nat \<times> 'el) \<Rightarrow> bool) \<Rightarrow> (nat \<times> 'el \<Rightarrow> bool)"
  where "sr_some sr = (\<lambda>(i,e). (\<exists> x. sr x (i,e)))"
definition r_some :: "('t \<Rightarrow> 'el \<Rightarrow> bool) \<Rightarrow> 'el \<Rightarrow> bool"
  where "r_some r = (\<lambda>e. (\<exists> x. r x e))"

lemma r_some_sr_some: 
 "r_some r \<circ> snd = sr_some (\<lambda>x. r x \<circ> snd)"
  apply(simp add: r_some_def sr_some_def split_def)
  by(rule ext,rule comp_apply)

lemma sr_elem_fst_map_indx: 
 "(sr_elem_fst_map pp a) = 
  (sp_elem_map (sr_some pp) a) \<circ>\<^sub>m (sr_indx_fst_map pp a)"
  apply(simp add: sr_elem_fst_map_def sr_indx_fst_map_def)
  apply(simp add: sp_elem_fst_indx)
  apply(rule ext)
  apply(simp add: sp_elem_map sr_some_def iexcerpt_def map_comp_def)
  apply(case_tac "sp_indx_fst (pp x) a",simp)
  apply(frule sp_indx_fst_valid,frule sp_indx_fst_satisfies_sp)
  by(simp,rule exI)

lemma ran_sr_indx_fst_map: 
 "ran (sr_indx_fst_map pp a) \<subseteq> dom (sp_elem_map (sr_some pp) a)"
  apply(simp add: ran_def)
  apply(rule subsetI,simp)
  apply(erule exE)
  apply(simp add: sr_indx_fst_map_def)
  apply(frule sp_indx_fst_satisfies_sp,drule sp_indx_fst_valid)
  apply(rule_tac b="a ! x" in domI)
  apply(simp add: sp_elem_map sr_some_def iexcerpt_def)
  by(rule exI)

lemma dom_sr_indx_fst_map:
 "dom (sr_indx_fst_map pp a) = dom (sr_elem_fst_map pp a)"
  apply(simp add: sr_elem_fst_map_def sr_indx_fst_map_def dom_def)
  apply(rule Collect_cong)
  by(auto simp add: sp_elem_fst_indx)

lemma sr_elem_fst_map_indx': 
 "(sr_elem_fst_map pp a) = 
  (elem_map a) \<circ>\<^sub>m (sr_indx_fst_map pp a)"
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

subsection \<open>Modification Functions\<close>

subsubsection \<open>Property Preservation\<close>

text \<open>
All modification functions preserve the length of the list. This can be 
expressed by the following predicate.
\<close>

definition prsvlen :: "('el list \<Rightarrow> 'el list) \<Rightarrow> bool"
  where "prsvlen u \<equiv> \<forall>x. length (u x) = length x"

lemma prsvlen[simp]: 
 "prsvlen u \<Longrightarrow> length (u x) = length x" 
  by(simp add: prsvlen_def)

text \<open>
All modification functions also preserve arbitrary properties for the elements,
if the element update function preserves this property. This can be 
expressed using the following predicates.
\<close>

definition elmsp :: "('el \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> bool"
  where "elmsp p \<equiv> \<lambda>x. \<forall>i. vld x i \<longrightarrow> p (nth x i)"
definition prsvp :: "('x \<Rightarrow> bool) \<Rightarrow> ('x \<Rightarrow> 'x) \<Rightarrow> bool"
  where "prsvp p f \<equiv> \<forall>x. p x \<longrightarrow> p (f x)"
abbreviation "prsvelmsp p \<equiv> prsvp (elmsp p)"

text \<open>
The lemma bucket \<open>lstp\<close> is introduced for \<open>prsvlen\<close>, \<open>prsvelmsp\<close> and \<open>elmsp\<close>
propositions about lists, list construction functions and list modification 
functions.
\<close>

ML \<open>structure lstp = Named_Thms (val name = Binding.name "lstp" val description = "")\<close>
setup \<open> lstp.setup \<close>

text \<open>
The rules for inferring \<open>prsvlen\<close>, \<open>prsvelmsp\<close> and \<open>elmsp\<close> properties for function 
and function application terms could be specified generically for all functions. 
However, for complex terms unification for such rules not always works. Therefore 
the locale \<open>Prsvlstp\<close> is introduced which generates specific rules for every 
list modification function when interpreted for the function. The rules are 
collected in bucket \<open>lstp\<close>.
\<close>

locale Prsvlstp =
  fixes f :: "'el list \<Rightarrow> 'el list"
  assumes prsvlen[simp]: "prsvlen f"
begin
lemma prsvlen_comp[simp]: "\<lbrakk>prsvlen f; prsvlen u\<rbrakk> \<Longrightarrow> prsvlen (f \<circ> u)"
  by(simp add: prsvlen_def)
lemma prsvlen_appl[simp]: "\<lbrakk>prsvlen f; prsvlen u\<rbrakk> \<Longrightarrow> prsvlen (\<lambda>x. f (u x))"
  by(simp add: prsvlen_def)
lemma elmspRule[lstp]: "\<lbrakk>elmsp p x; prsvelmsp p f\<rbrakk> \<Longrightarrow> elmsp p (f x)"
  by(simp add: prsvp_def)
lemma prsvelmsp_comp[lstp]: "\<lbrakk>prsvelmsp p f; prsvelmsp p u\<rbrakk> \<Longrightarrow> prsvelmsp p (f \<circ> u)"
  by(simp add: prsvp_def)
lemma prsvelmsp_appl[lstp]: "\<lbrakk>prsvelmsp p f; prsvelmsp p u\<rbrakk> \<Longrightarrow> prsvelmsp p (\<lambda>x. f (u x))"
  by(simp add: prsvp_def)
lemmas rules = prsvlen prsvlen_comp prsvlen_appl elmspRule prsvelmsp_comp prsvelmsp_appl
end

lemma elmsp_top[lstp]:
 "elmsp \<top> x"
  by(simp add: elmsp_def)
lemma prsvelmsp_top[lstp]:
 "prsvelmsp \<top> u"
  by(simp add: prsvp_def lstp)

text \<open>
A list update function must satisfy \<open>prsvlen\<close> and possibly a \<open>prsvelmsp\<close> property, therefore a 
rule is added to the \<open>lstp\<close> bucket for inferring the preservation of a conjunction of two properties.
\<close>

lemma prsvp_conj[lstp]: "\<lbrakk>prsvp p1 f; prsvp p2 f\<rbrakk> \<Longrightarrow> prsvp (\<lambda>x. p1 x \<and> p2 x) f"
  by(simp add: prsvp_def)

subsubsection \<open>Definitions\<close>

text \<open>
The most basic modification function modifies the elements in an array excerpt. 
The new element values are specified by an element constructor function, they 
may depend on the old ones (e) and on the position (i) in the array.
\<close>
definition spie_elem_upd :: "(nat \<times> 'el \<Rightarrow> bool) \<Rightarrow> (nat \<times> 'el \<Rightarrow> 'el) \<Rightarrow> 'el list \<Rightarrow> 'el list"
  where "spie_elem_upd sp u \<equiv> (\<lambda>a. map (override_on snd u (Collect sp)) (enumerate 0 a))"

lemma prsvelmsp_spie_elem_upd [lstp]: 
 "\<forall>i. prsvp p (\<lambda>x. u (i,x)) \<Longrightarrow> prsvelmsp p (spie_elem_upd sp u)"
  apply(auto simp add: spie_elem_upd_def prsvp_def elmsp_def)
  by (metis nth_enumerate_eq override_on_apply_in override_on_apply_notin snd_conv)
interpretation Prsvlstp_spie_elem_upd: Prsvlstp "spie_elem_upd sp u"
  by(unfold_locales,simp add: spie_elem_upd_def prsvlen_def)

text \<open>
Simplified forms where the excerpt is determined by index or element value alone or is the whole array
and the new element values depend on the index or old value alone or are specified by a constant.
\<close>

definition spi_elem_upd :: "(nat \<times> 'el \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> 'el) \<Rightarrow> 'el list \<Rightarrow> 'el list"
  where "spi_elem_upd sp u \<equiv> spie_elem_upd sp (u\<circ>fst)"
definition spe_elem_upd :: "(nat \<times> 'el \<Rightarrow> bool) \<Rightarrow> ('el \<Rightarrow> 'el) \<Rightarrow> 'el list \<Rightarrow> 'el list"
  where "spe_elem_upd sp u \<equiv> spie_elem_upd sp (u\<circ>snd)"
definition sp_elem_upd :: "(nat \<times> 'el \<Rightarrow> bool) \<Rightarrow> 'el \<Rightarrow> 'el list \<Rightarrow> 'el list"
  where "sp_elem_upd sp v \<equiv> spie_elem_upd sp (\<lambda>_.v)"
definition sie_elem_upd :: "(nat \<Rightarrow> bool) \<Rightarrow> (nat \<times> 'el \<Rightarrow> 'el) \<Rightarrow> 'el list \<Rightarrow> 'el list"
  where "sie_elem_upd s u \<equiv> spie_elem_upd (s\<circ>fst) u"
definition si_elem_upd :: "(nat \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> 'el) \<Rightarrow> 'el list \<Rightarrow> 'el list"
  where "si_elem_upd s u \<equiv> spie_elem_upd (s\<circ>fst) (u\<circ>fst)"
definition se_elem_upd :: "(nat \<Rightarrow> bool) \<Rightarrow> ('el \<Rightarrow> 'el) \<Rightarrow> 'el list \<Rightarrow> 'el list"
  where "se_elem_upd s u \<equiv> spie_elem_upd (s\<circ>fst) (u\<circ>snd)"
definition s_elem_upd :: "(nat \<Rightarrow> bool) \<Rightarrow> 'el \<Rightarrow> 'el list \<Rightarrow> 'el list"
  where "s_elem_upd s v \<equiv> spie_elem_upd (s\<circ>fst) ((\<lambda>_.v)\<circ>snd)"
definition pie_elem_upd :: "('el \<Rightarrow> bool) \<Rightarrow> (nat \<times> 'el \<Rightarrow> 'el) \<Rightarrow> 'el list \<Rightarrow> 'el list"
  where "pie_elem_upd p u \<equiv> spie_elem_upd (p\<circ>snd) u"
definition pi_elem_upd :: "('el \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> 'el) \<Rightarrow> 'el list \<Rightarrow> 'el list"
  where "pi_elem_upd p u \<equiv> spie_elem_upd (p\<circ>snd) (u\<circ>fst)"
definition pe_elem_upd :: "('el \<Rightarrow> bool) \<Rightarrow> ('el \<Rightarrow> 'el) \<Rightarrow> 'el list \<Rightarrow> 'el list"
  where "pe_elem_upd p u \<equiv> spie_elem_upd (p\<circ>snd) (u\<circ>snd)"
definition p_elem_upd :: "('el \<Rightarrow> bool) \<Rightarrow> 'el \<Rightarrow> 'el list \<Rightarrow> 'el list"
  where "p_elem_upd p v \<equiv> spie_elem_upd (p\<circ>snd) ((\<lambda>_.v)\<circ>snd)"
definition ie_elem_upd :: "(nat \<times> 'el \<Rightarrow> 'el) \<Rightarrow> 'el list \<Rightarrow> 'el list"
  where "ie_elem_upd u \<equiv> spie_elem_upd \<top> u"
definition i_elem_upd :: "(nat \<Rightarrow> 'el) \<Rightarrow> 'el list \<Rightarrow> 'el list"
  where "i_elem_upd u \<equiv> spie_elem_upd \<top> (u\<circ>fst)"
definition e_elem_upd :: "('el \<Rightarrow> 'el) \<Rightarrow> 'el list \<Rightarrow> 'el list"
  where "e_elem_upd u \<equiv> spie_elem_upd \<top> (u\<circ>snd)"
definition elem_upd :: "'el \<Rightarrow> 'el list \<Rightarrow> 'el list"
  where "elem_upd v \<equiv> spie_elem_upd \<top> ((\<lambda>_.v)\<circ>snd)"

text \<open>
Rules for inferring \<open>prsvlen\<close>, \<open>prsvelmsp\<close> and \<open>elmsp\<close> properties.
\<close>

lemma prsvelmsp_spi_elem_upd [lstp]: 
 "\<forall>i. p (u i) \<Longrightarrow> prsvelmsp p (spi_elem_upd sp u)"
  apply(unfold spi_elem_upd_def)
  apply(rule prsvelmsp_spie_elem_upd)
  by(simp add: prsvp_def)
interpretation Prsvlstp_spi_elem_upd: Prsvlstp "spi_elem_upd sp u"
  by(unfold_locales,simp add: spi_elem_upd_def lstp)
lemma prsvelmsp_spe_elem_upd [lstp]: 
 "prsvp p u \<Longrightarrow> prsvelmsp p (spe_elem_upd sp u)"
  by(simp add: spe_elem_upd_def lstp)
interpretation Prsvlstp_spe_elem_upd: Prsvlstp "spe_elem_upd sp u"
  by(unfold_locales,simp add: spe_elem_upd_def lstp)
lemma prsvelmsp_sp_elem_upd [lstp]: 
 "p v \<Longrightarrow> prsvelmsp p (sp_elem_upd sp v)"
  apply(unfold sp_elem_upd_def)
  apply(rule prsvelmsp_spie_elem_upd)
  by(simp add: prsvp_def)
interpretation Prsvlstp_sp_elem_upd: Prsvlstp "sp_elem_upd sp v"
  by(unfold_locales,simp add: sp_elem_upd_def lstp)
lemma prsvelmsp_sie_elem_upd [lstp]: 
 "\<forall>i. prsvp p (\<lambda>x. u (i,x)) \<Longrightarrow> prsvelmsp p (sie_elem_upd sp u)"
  by(simp add: sie_elem_upd_def lstp)
interpretation Prsvlstp_sie_elem_upd: Prsvlstp "sie_elem_upd sp u"
  by(unfold_locales,simp add: sie_elem_upd_def lstp)
lemma prsvelmsp_si_elem_upd [lstp]: 
 "\<forall>i. p (u i) \<Longrightarrow> prsvelmsp p (si_elem_upd sp u)"
  apply(unfold si_elem_upd_def)
  apply(rule prsvelmsp_spie_elem_upd)
  by(simp add: prsvp_def)
interpretation Prsvlstp_si_elem_upd: Prsvlstp "si_elem_upd sp u"
  by(unfold_locales,simp add: si_elem_upd_def lstp)
lemma prsvelmsp_se_elem_upd [lstp]: 
 "prsvp p u \<Longrightarrow> prsvelmsp p (se_elem_upd sp u)"
  by(simp add: se_elem_upd_def lstp)
interpretation Prsvlstp_se_elem_upd: Prsvlstp "se_elem_upd sp u"
  by(unfold_locales,simp add: se_elem_upd_def lstp)
lemma prsvelmsp_s_elem_upd [lstp]: 
 "p v \<Longrightarrow> prsvelmsp p (s_elem_upd sp v)"
  apply(unfold s_elem_upd_def)
  apply(rule prsvelmsp_spie_elem_upd)
  by(simp add: prsvp_def)
interpretation Prsvlstp_s_elem_upd: Prsvlstp "s_elem_upd sp u"
  by(unfold_locales,simp add: s_elem_upd_def lstp)
lemma prsvelmsp_pie_elem_upd [lstp]: 
 "\<forall>i. prsvp p (\<lambda>x. u (i,x)) \<Longrightarrow> prsvelmsp p (pie_elem_upd sp u)"
  by(auto simp add: pie_elem_upd_def lstp)
interpretation Prsvlstp_pie_elem_upd: Prsvlstp "pie_elem_upd sp u"
  by(unfold_locales,simp add: pie_elem_upd_def lstp)
lemma prsvelmsp_pi_elem_upd [lstp]: 
 "\<forall>i. p (u i) \<Longrightarrow> prsvelmsp p (pi_elem_upd sp u)"
  apply(unfold pi_elem_upd_def)
  apply(rule prsvelmsp_spie_elem_upd)
  by(simp add: prsvp_def)
interpretation Prsvlstp_pi_elem_upd: Prsvlstp "pi_elem_upd sp u"
  by(unfold_locales,simp add: pi_elem_upd_def lstp)
lemma prsvelmsp_pe_elem_upd [lstp]: 
 "prsvp p u \<Longrightarrow> prsvelmsp p (pe_elem_upd sp u)"
  by(simp add: pe_elem_upd_def lstp)
interpretation Prsvlstp_pe_elem_upd: Prsvlstp "pe_elem_upd sp u"
  by(unfold_locales,simp add: pe_elem_upd_def lstp)
lemma prsvelmsp_p_elem_upd [lstp]: 
 "p v \<Longrightarrow> prsvelmsp p (p_elem_upd sp v)"
  apply(unfold p_elem_upd_def)
  apply(rule prsvelmsp_spie_elem_upd)
  by(simp add: prsvp_def)
interpretation Prsvlstp_p_elem_upd: Prsvlstp "p_elem_upd sp u"
  by(unfold_locales,simp add: p_elem_upd_def lstp)
lemma prsvelmsp_ie_elem_upd [lstp]: 
 "\<forall>i. prsvp p (\<lambda>x. u (i,x)) \<Longrightarrow> prsvelmsp p (ie_elem_upd u)"
  by(auto simp add: ie_elem_upd_def lstp)
interpretation Prsvlstp_ie_elem_upd: Prsvlstp "ie_elem_upd u"
  by(unfold_locales,simp add: ie_elem_upd_def lstp)
lemma prsvelmsp_i_elem_upd [lstp]: 
 "\<forall>i. p (u i) \<Longrightarrow> prsvelmsp p (i_elem_upd u)"
  apply(unfold i_elem_upd_def)
  apply(rule prsvelmsp_spie_elem_upd)
  by(simp add: prsvp_def)
interpretation Prsvlstp_i_elem_upd: Prsvlstp "i_elem_upd u"
  by(unfold_locales,simp add: i_elem_upd_def lstp)
lemma prsvelmsp_e_elem_upd [lstp]: 
 "prsvp p u \<Longrightarrow> prsvelmsp p (e_elem_upd u)"
  by(simp add: e_elem_upd_def lstp)
interpretation Prsvlstp_e_elem_upd: Prsvlstp "e_elem_upd u"
  by(unfold_locales,simp add: e_elem_upd_def lstp)
lemma prsvelmsp_elem_upd [lstp]: 
 "p v \<Longrightarrow> prsvelmsp p (elem_upd v)"
  apply(unfold elem_upd_def)
  apply(rule prsvelmsp_spie_elem_upd)
  by(simp add: prsvp_def)
interpretation Prsvlstp_elem_upd: Prsvlstp "elem_upd v"
  by(unfold_locales,simp add: elem_upd_def lstp)

text \<open>
Alternative standalone definitions. We do not use \<open>iexcerpt\<close> here because the modification
functions work on lists and the indexes are always valid.
\<close>
lemma spie_elem_upd: 
  "spie_elem_upd sp u = (\<lambda>a. [(if sp (i,(nth a i)) then u (i,(nth a i)) else (nth a i)).  i \<leftarrow> [0..< length a]])"
  apply(simp add: spie_elem_upd_def enumerate_eq_zip override_on_def)
  apply(rule ext)
  by(rule nth_equalityI,simp_all)
lemma spi_elem_upd: 
  "spi_elem_upd sp u = (\<lambda>a. [(if sp (i,(nth a i)) then u i else (nth a i)).  i \<leftarrow> [0..< length a]])"
  by(auto simp add: spi_elem_upd_def spie_elem_upd)
lemma spe_elem_upd: 
  "spe_elem_upd sp u = (\<lambda>a. [(if sp (i,(nth a i)) then u (nth a i) else (nth a i)).  i \<leftarrow> [0..< length a]])"
  by(auto simp add: spe_elem_upd_def spie_elem_upd)
lemma sp_elem_upd: 
  "sp_elem_upd sp v = (\<lambda>a. [(if sp (i,(nth a i)) then v else (nth a i)).  i \<leftarrow> [0..< length a]])"
  by(simp add: sp_elem_upd_def spie_elem_upd)
lemma sie_elem_upd: 
  "sie_elem_upd s u = (\<lambda>a. [(if s i then u (i,(nth a i)) else (nth a i)).  i \<leftarrow> [0..< length a]])"
  by(simp add: sie_elem_upd_def spie_elem_upd)
lemma si_elem_upd: 
  "si_elem_upd s u = (\<lambda>a. [(if s i then u i else (nth a i)).  i \<leftarrow> [0..< length a]])"
  by(auto simp add: si_elem_upd_def spie_elem_upd)
lemma se_elem_upd: 
  "se_elem_upd s u = (\<lambda>a. [(if s i then u (nth a i) else (nth a i)).  i \<leftarrow> [0..< length a]])"
  by(auto simp add: se_elem_upd_def spie_elem_upd)
lemma s_elem_upd: 
  "s_elem_upd s v = (\<lambda>a. [(if s i then v else (nth a i)).  i \<leftarrow> [0..< length a]])"
  by(simp add: s_elem_upd_def spie_elem_upd comp_def)
lemma pie_elem_upd: 
  "pie_elem_upd p u = (\<lambda>a. [(if p (nth a i) then u (i,(nth a i)) else (nth a i)).  i \<leftarrow> [0..< length a]])"
  by(simp add: pie_elem_upd_def spie_elem_upd)
lemma pi_elem_upd: 
  "pi_elem_upd p u = (\<lambda>a. [(if p (nth a i) then u i else (nth a i)).  i \<leftarrow> [0..< length a]])"
  by(auto simp add: pi_elem_upd_def spie_elem_upd)
lemma pe_elem_upd: 
  "pe_elem_upd p u = (\<lambda>a. [(if p (nth a i) then u (nth a i) else (nth a i)).  i \<leftarrow> [0..< length a]])"
  by(auto simp add: pe_elem_upd_def spie_elem_upd)
lemma p_elem_upd: 
  "p_elem_upd p v = (\<lambda>a. [(if p (nth a i) then v else (nth a i)).  i \<leftarrow> [0..< length a]])"
  by(simp add: p_elem_upd_def spie_elem_upd comp_def)
lemma ie_elem_upd: 
  "ie_elem_upd u = (\<lambda>a. [u (i,(nth a i)).  i \<leftarrow> [0..< length a]])"
  by(simp add: ie_elem_upd_def spie_elem_upd)
lemma i_elem_upd: 
  "i_elem_upd u = (\<lambda>a. map u [0..< length a])"
  by(simp add: i_elem_upd_def spie_elem_upd)
lemma e_elem_upd: 
  "e_elem_upd u = map u"
  apply(rule ext)
  apply(simp add: e_elem_upd_def spie_elem_upd)
  by(rule nth_equalityI,simp_all)
lemma elem_upd: 
  "elem_upd v = (\<lambda>a. replicate (length a) v)"
  by(simp add: elem_upd_def spie_elem_upd map_replicate_const)

subsubsection \<open>Excerpt Unions\<close>

text \<open>
Updating a union of excerpts can be done by sequentially updating the excerpts.
If the new value depends on the old value the excerpts must be disjunct.
If also the excerpts depend on the element, the excerpt of the second update must take 
the first update into account.
\<close>
lemma spie_elem_upd_SP_union:
 "(sp1 \<circ>\<^sub>2 u) \<sqinter> sp2 = \<bottom> \<Longrightarrow>
  spie_elem_upd (sp1 \<squnion> sp2) u = (spie_elem_upd sp1 u) \<circ> (spie_elem_upd sp2 u)"
  apply(rule ext,auto simp add: spie_elem_upd comp_snd_def)
  by(drule_tac x="(xa, x ! xa)" in fun_cong,simp)
lemma spi_elem_upd_SP_union:
 "spi_elem_upd (sp1 \<squnion> sp2) u = (spi_elem_upd sp1 u) \<circ> (spi_elem_upd sp2 u)"
  by(rule ext,auto simp add: spi_elem_upd comp_snd_def)
lemma spe_elem_upd_SP_union:
 "(sp1 \<circ>\<^sub>2 (u \<circ> snd)) \<sqinter> sp2 = \<bottom> \<Longrightarrow>
  spe_elem_upd (sp1 \<squnion> sp2) u = (spe_elem_upd sp1 u) \<circ> (spe_elem_upd sp2 u)"
  by(simp add: spe_elem_upd_def spie_elem_upd_SP_union)
lemma sp_elem_upd_SP_union:
 "sp_elem_upd (sp1 \<squnion> sp2) v = (sp_elem_upd sp1 v) \<circ> (sp_elem_upd sp2 v)"
  by(rule ext,auto simp add: sp_elem_upd)
lemma sie_elem_upd_S_union:
 "s1 \<sqinter> s2 = \<bottom> \<Longrightarrow>
  sie_elem_upd (s1 \<squnion> s2) u = (sie_elem_upd s1 u) \<circ> (sie_elem_upd s2 u)"
  apply(rule ext,auto simp add: sie_elem_upd)
  by(drule_tac x="xa" in fun_cong,simp)
lemma si_elem_upd_S_union:
 "si_elem_upd (s1 \<squnion> s2) u = (si_elem_upd s1 u) \<circ> (si_elem_upd s2 u)"
  by(rule ext,auto simp add: si_elem_upd)
lemma se_elem_upd_S_union:
 "s1 \<sqinter> s2 = \<bottom> \<Longrightarrow>
  se_elem_upd (s1 \<squnion> s2) u = (se_elem_upd s1 u) \<circ> (se_elem_upd s2 u)"
  by(unfold se_elem_upd_def,fold sie_elem_upd_def, simp add: sie_elem_upd_S_union)
lemma s_elem_upd_S_union:
 "s_elem_upd (s1 \<squnion> s2) v = (s_elem_upd s1 v) \<circ> (s_elem_upd s2 v)"
  by(rule ext,auto simp add: s_elem_upd)
lemma pie_elem_upd_P_union:
 "(p1 \<circ> u) \<sqinter> (p2 \<circ> snd) = \<bottom> \<Longrightarrow>
  pie_elem_upd (p1 \<squnion> p2) u = (pie_elem_upd p1 u) \<circ> (pie_elem_upd p2 u)"
  apply(rule ext,auto simp add: pie_elem_upd)
  by(drule_tac x="(xa, x ! xa)" in fun_cong,simp)
lemma pi_elem_upd_P_union:
 "pi_elem_upd (p1 \<squnion> p2) u = (pi_elem_upd p1 u) \<circ> (pi_elem_upd p2 u)"
  by(rule ext,auto simp add: pi_elem_upd)
lemma pe_elem_upd_P_union:
 "(p1 \<circ> u) \<sqinter> p2 = \<bottom> \<Longrightarrow>
  pe_elem_upd (p1 \<squnion> p2) u = (pe_elem_upd p1 u) \<circ> (pe_elem_upd p2 u)"
  apply(rule ext,auto simp add: pe_elem_upd)
  by(drule_tac x=" x ! xa" in fun_cong,simp)
lemma p_elem_upd_P_union:
 "p_elem_upd (p1 \<squnion> p2) v = (p_elem_upd p1 v) \<circ> (p_elem_upd p2 v)"
  by(rule ext,auto simp add: p_elem_upd)

lemmas upd_union[THEN fun_cong,simplified,symmetric] = 
  spie_elem_upd_SP_union
  spi_elem_upd_SP_union
  spe_elem_upd_SP_union
  sp_elem_upd_SP_union
  sie_elem_upd_S_union
  si_elem_upd_S_union
  se_elem_upd_S_union
  s_elem_upd_S_union
  pie_elem_upd_P_union
  pi_elem_upd_P_union
  pe_elem_upd_P_union
  p_elem_upd_P_union

subsubsection \<open>Empty Excerpts\<close>

text \<open>
Updating the empty excerpt is a no-op.
\<close>
lemma spie_elem_upd_SP_bot: "spie_elem_upd \<bottom> u a = a"
  by(simp add: spie_elem_upd map_nth)
lemma spi_elem_upd_SP_bot: "spi_elem_upd \<bottom> u a = a"
  by(simp add: spi_elem_upd map_nth)
lemma spe_elem_upd_SP_bot: "spe_elem_upd \<bottom> u a = a"
  by(simp add: spe_elem_upd map_nth)
lemma sp_elem_upd_SP_bot: "sp_elem_upd \<bottom> u a = a"
  by(simp add: sp_elem_upd map_nth)
lemma sie_elem_upd_S_bot: "sie_elem_upd \<bottom> u a = a"
  by(simp add: sie_elem_upd map_nth)
lemma si_elem_upd_S_bot: "si_elem_upd \<bottom> u a = a"
  by(simp add: si_elem_upd map_nth)
lemma se_elem_upd_S_bot: "se_elem_upd \<bottom> u a = a"
  by(simp add: se_elem_upd map_nth)
lemma s_elem_upd_S_bot: "s_elem_upd \<bottom> u a = a"
  by(simp add: s_elem_upd map_nth)
lemma pie_elem_upd_P_bot: "pie_elem_upd \<bottom> u a = a"
  by(simp add: pie_elem_upd map_nth)
lemma pi_elem_upd_P_bot: "pi_elem_upd \<bottom> u a = a"
  by(simp add: pi_elem_upd map_nth)
lemma pe_elem_upd_P_bot: "pe_elem_upd \<bottom> u a = a"
  by(simp add: pe_elem_upd map_nth)
lemma p_elem_upd_P_bot: "p_elem_upd \<bottom> u a = a"
  by(simp add: p_elem_upd map_nth)

lemmas upd_bot = 
  spie_elem_upd_SP_bot
  spi_elem_upd_SP_bot
  spe_elem_upd_SP_bot
  sp_elem_upd_SP_bot
  sie_elem_upd_S_bot
  si_elem_upd_S_bot
  se_elem_upd_S_bot
  s_elem_upd_S_bot
  pie_elem_upd_P_bot
  pi_elem_upd_P_bot
  pe_elem_upd_P_bot
  p_elem_upd_P_bot

subsubsection \<open>Whole Array Excerpts\<close>

text \<open>
If for an excerpt update the update does not change the elements outside the excerpt,
the update can be applied to the whole array. 
\<close>
lemma sp_to_p_ie_elem_upd:
 "\<forall>i<length a. sp (i,nth a i) \<noteq> p (nth a i) \<longrightarrow> (nth a i) = u (i,nth a i) \<Longrightarrow> 
  spie_elem_upd sp u a = pie_elem_upd p u a"
  by(simp add: pie_elem_upd_def spie_elem_upd)
lemma sp_to_p_i_elem_upd:
 "\<forall>i<length a. sp (i,nth a i) \<noteq> p (nth a i) \<longrightarrow> (nth a i) = u i \<Longrightarrow> 
  spi_elem_upd sp u a = pi_elem_upd p u a"
  by(simp add: pi_elem_upd_def spi_elem_upd_def spie_elem_upd)
lemma sp_to_p_e_elem_upd:
 "\<forall>i<length a. sp (i,nth a i) \<noteq> p (nth a i) \<longrightarrow> (nth a i) = u (nth a i) \<Longrightarrow> 
  spe_elem_upd sp u a = pe_elem_upd p u a"
  by(simp add: pe_elem_upd_def spe_elem_upd_def spie_elem_upd)
lemma sp_to_p_elem_upd:
 "\<forall>i<length a. sp (i,nth a i) \<noteq> p (nth a i) \<longrightarrow> (nth a i) = v \<Longrightarrow> 
  sp_elem_upd sp v a = p_elem_upd p v a"
  by(simp add: p_elem_upd_def sp_elem_upd_def spie_elem_upd)

lemma s_to_ie_elem_upd:
 "\<forall>i<length a. \<not> s i \<longrightarrow> (nth a i) = u (i,nth a i) \<Longrightarrow> 
  sie_elem_upd s u a = ie_elem_upd u a"
  by(simp add: ie_elem_upd_def sie_elem_upd spie_elem_upd)
lemma s_to_i_elem_upd:
 "\<forall>i<length a. \<not> s i \<longrightarrow> (nth a i) = u i \<Longrightarrow> 
  si_elem_upd s u a = i_elem_upd u a"
  by(simp add: i_elem_upd_def si_elem_upd_def spie_elem_upd)
lemma s_to_e_elem_upd:
 "\<forall>i<length a. \<not> s i \<longrightarrow> (nth a i) = u (nth a i) \<Longrightarrow> 
  se_elem_upd s u a = e_elem_upd u a"
  by(simp add: e_elem_upd_def se_elem_upd_def spie_elem_upd)
lemma s_to_elem_upd:
 "\<forall>i<length a. \<not> s i \<longrightarrow> (nth a i) = v \<Longrightarrow> 
  s_elem_upd s v a = elem_upd v a"
  by(simp add: elem_upd_def s_elem_upd_def spie_elem_upd)

lemma sp_to_s_ie_elem_upd:
 "\<forall>i<length a. sp (i,nth a i) \<noteq> s i \<longrightarrow> (nth a i) = u (i,nth a i) \<Longrightarrow> 
  spie_elem_upd sp u a = sie_elem_upd s u a"
  by(simp add: sie_elem_upd_def spie_elem_upd)
lemma sp_to_s_i_elem_upd:
 "\<forall>i<length a. sp (i,nth a i) \<noteq> s i \<longrightarrow> (nth a i) = u i \<Longrightarrow> 
  spi_elem_upd sp u a = si_elem_upd s u a"
  by(simp add: si_elem_upd_def spi_elem_upd_def spie_elem_upd)
lemma sp_to_s_e_elem_upd:
 "\<forall>i<length a. sp (i,nth a i) \<noteq> s i \<longrightarrow> (nth a i) = u (nth a i) \<Longrightarrow> 
  spe_elem_upd sp u a = se_elem_upd s u a"
  by(simp add: se_elem_upd_def spe_elem_upd_def spie_elem_upd)
lemma sp_to_s_elem_upd:
 "\<forall>i<length a. sp (i,nth a i) \<noteq> s i \<longrightarrow> (nth a i) = v \<Longrightarrow> 
  sp_elem_upd sp v a = s_elem_upd s v a"
  by(simp add: s_elem_upd_def sp_elem_upd_def spie_elem_upd)

lemma p_to_ie_elem_upd:
 "\<forall>i<length a. \<not> p (nth a i) \<longrightarrow> (nth a i) = u (i,nth a i) \<Longrightarrow> 
  pie_elem_upd p u a = ie_elem_upd u a"
  by(simp add: ie_elem_upd_def pie_elem_upd spie_elem_upd)
lemma p_to_i_elem_upd:
 "\<forall>i<length a. \<not> p (nth a i) \<longrightarrow> (nth a i) = u i \<Longrightarrow> 
  pi_elem_upd p u a = i_elem_upd u a"
  by(simp add: i_elem_upd_def pi_elem_upd_def spie_elem_upd)
lemma p_to_e_elem_upd:
 "\<forall>i<length a. \<not> p (nth a i) \<longrightarrow> (nth a i) = u (nth a i) \<Longrightarrow> 
  pe_elem_upd p u a = e_elem_upd u a"
  by(simp add: e_elem_upd_def pe_elem_upd_def spie_elem_upd)
lemma p_to_elem_upd:
 "\<forall>i<length a. \<not> p (nth a i) \<longrightarrow> (nth a i) = v \<Longrightarrow> 
  p_elem_upd p v a = elem_upd v a"
  by(simp add: elem_upd_def p_elem_upd_def spie_elem_upd)

subsubsection \<open>Observing Updates\<close>

text \<open>
The basic rule derives an observation on an updated array by splitting the observed excerpt \<open>sp\<close>
into the updated and the non-updated part and adding the observations on them. 

The observation on the updated excerpt \<open>sp'\<close> can then be constructed by converting the original
observation on \<open>sp'\<close> to an iemap, composing it with an element conversion map and a restriction
map for \<open>sp\<close> and converting it back to an element map.

The function \<open>update_iemap\<close> builds the element conversion map from the element constructor function
\<open>u\<close>. The function \<open>sp_upd_map\<close> composes all iemaps starting with the old observation \<open>sp_elem_map\<close>
on the updated excerpt \<open>sp'\<close>, resulting in the updated observation on the updated excerpt.

Since excerpts may also depend on element values, the element constructor function \<open>u\<close> generally 
also modifies the excerpt on which the updated observation is defined. The function
\<open>sp_upd\<close> is defined to determine a new excerpt from \<open>sp'\<close> and \<open>u\<close> which covers all updated elements.
It may also cover unchanged elements, if they 
\<close>

definition update_iemap :: "(nat \<times> 'el \<Rightarrow> 'el) \<Rightarrow> (nat \<times> 'el \<rightharpoonup> nat \<times> 'el)"
  where "update_iemap u = Some \<circ> (id \<circ>\<^sub>2 u)"
definition sp_upd_map :: "(nat \<times> 'el \<Rightarrow> bool) \<Rightarrow> (nat \<times> 'el \<Rightarrow> bool) \<Rightarrow> (nat \<times> 'el \<Rightarrow> 'el) \<Rightarrow> 'el list \<Rightarrow> (nat \<rightharpoonup> 'el)"
  where "sp_upd_map sp sp' u \<equiv> map_of \<circ> (filter sp) \<circ> (map (id \<circ>\<^sub>2 u)) \<circ> (filter sp') \<circ> (enumerate 0)"
definition sp_upd :: "(nat \<times> 'el \<Rightarrow> bool) \<Rightarrow> (nat \<times> 'el \<Rightarrow> 'el) \<Rightarrow> (nat \<times> 'el \<Rightarrow> bool)"
  where "sp_upd sp' u \<equiv> \<lambda>(i,e). \<exists>e'. e = u (i,e') \<and> sp' (i,e')"

text \<open>
\<close>

lemma sp_upd_map:
 "sp_upd_map sp sp' u a =
  from_iemap \<circ>\<^sub>m (sp_restrict_iemap sp) \<circ>\<^sub>m (update_iemap u) \<circ>\<^sub>m (make_iemap (sp_elem_map sp' a))"
  apply(rule ext)
  apply(simp add: sp_upd_map_def make_iemap update_iemap_def sp_restrict_iemap_def from_iemap_def)
  apply(simp add: map_comp_def sp_elem_map iexcerpt_def comp_snd_def restrict_map_def)
  apply(auto simp add: map_of_eq_None_iff image_def in_set_enumerate_eq)
  apply(rule map_of_is_SomeI)
    apply(rule distinct_map_filter,simp add: comp_def split_def)
   apply(rule distinct_map_filter,simp)
  by(simp add: image_def in_set_enumerate_eq)

text \<open>
The main theorem for observing updates. It splits the observation in two summands
with disjunct domains.
\<close>

lemma dom_sp_elem_map_diff:
 "dom (sp_elem_map (sp-sp') a) = dom (sp_elem_map (- sp') a) \<inter> dom (sp_elem_map sp a)"
  apply(fold sp_indx_set_def)
  by(auto simp add: sp_indx_set iexcerpt_def)

lemma dom_sp_upd_map:
 "dom (sp_upd_map sp sp' u a) = dom (sp_elem_map sp' a) \<inter> dom(sp_elem_map (sp \<circ>\<^sub>2 u) a)"
  apply(simp add: sp_upd_map_def)
  apply(simp add: dom_map_of_conv_image_fst image_def comp_snd_def in_set_enumerate_eq)
  apply(fold sp_indx_set_def)
  by(auto simp add: sp_indx_set iexcerpt_def)

lemma disjunct_dom_sp_elem_upd_map:
 "dom (sp_elem_map (sp-sp') a) \<inter> dom (sp_upd_map sp sp' u a) = {}"
  apply(simp add: dom_sp_elem_map_diff dom_sp_upd_map)
  apply(fold sp_indx_set_def)
  by(auto simp add: sp_indx_set iexcerpt_def)

theorem observe_update:
 "sp_elem_map sp (spie_elem_upd sp' u a) = 
  (sp_elem_map (sp-sp') a) ++ (sp_upd_map sp sp' u a)"
  (* unfold definitions *)
  apply(simp add: sp_upd_map_def sp_elem_map_def spie_elem_upd_def override_on_def)
  (* introduce index i and corresponding element e for the left hand side *)
  apply(subst map_of_append[symmetric])
  apply(rule map_of_eqI)
  apply(clarsimp simp add: image_def in_set_enumerate_eq override_on_def comp_snd_def)
   apply(subst Collect_disj_eq[symmetric])
   apply(rule Collect_cong)
  apply(case_tac "sp' (y, a ! y)")
   apply(auto simp add: nth_enumerate_eq)
  apply(rename_tac i e)
  (* assume i is in the domain of the second summand, then the first one can be omitted *)
  apply(case_tac "i \<in> dom (sp_upd_map sp sp' u a)")
  apply(clarsimp simp add: sp_upd_map_def comp_snd_def)
   apply(rule map_of_is_SomeI,rule distinct_map_filter,simp add: enumerate_eq_zip)
  apply(drule map_of_SomeD)
   apply(simp add: in_set_enumerate_eq image_def)
   apply(erule conjE,subst (asm) nth_map,simp)
   apply(simp add: nth_enumerate_eq)
  (* swap summands, that is possible because their domains are disjunct *)
  apply(subst map_add_comm)
   apply(insert disjunct_dom_sp_elem_upd_map)[1]
   apply(simp add: sp_elem_map_def sp_upd_map_def,fast)
  (* assume i is in the domain of the second summand, then the first one can be omitted *)
  apply(case_tac "i \<in> dom (sp_elem_map (sp-sp') a)")
  apply(clarsimp simp add: sp_elem_map_def sp_upd_map_def comp_snd_def)
  apply(rule_tac x=e in exI)
   apply(rule map_of_is_SomeI)
    apply(rule distinct_map_filter,simp add: comp_def split_def)
    apply(rule distinct_map_filter,simp)
  apply(simp add: in_set_enumerate_eq image_def)
  apply(erule conjE,subst (asm) nth_map,simp)
   apply(simp add: nth_enumerate_eq)
   apply(subst (asm) map_of_eq_Some_iff)
    apply(rule distinct_map_filter,simp add: enumerate_eq_zip)
  apply(drule map_of_SomeD)
    apply(simp add: in_set_enumerate_eq nth_enumerate_eq)
  (* remaining case: i is in the domain of neither summand, leads to contradiction *)
  apply(simp add: sp_upd_map_def sp_elem_map_def domIff)
  apply(simp add: map_of_eq_None_iff image_def in_set_enumerate_eq comp_snd_def)
  apply(erule conjE,subst (asm) nth_map,simp)
  apply(auto simp add: nth_enumerate_eq)
  by(case_tac "sp' (i, a ! i)",simp_all add: nth_enumerate_eq)

text \<open>
If the updated and observed excerpts do not overlap the updates cannot be observed.
\<close>

lemma sp_upd_map_empty:
 "sp \<sqinter> sp_upd sp' u = \<bottom> \<Longrightarrow>
  sp_upd_map sp sp' u a = Map.empty"
  apply(simp add: sp_upd_map sp_upd_def)
  apply(rule ext)
  apply(simp add: map_comp_def from_iemap_def sp_restrict_iemap_def update_iemap_def make_iemap)
  apply(auto simp add: comp_snd_def sp_elem_map iexcerpt_def restrict_map_def)
  by(drule_tac x="(x,u (x,a!x))" in disjoint_pred,simp)

lemma observe_update_no_update:
 "\<lbrakk>sp \<sqinter> sp' = \<bottom>; sp \<sqinter> sp_upd sp' u = \<bottom>\<rbrakk> \<Longrightarrow>
  sp_elem_map sp (spie_elem_upd sp' u a) = sp_elem_map sp a"
  by(simp add: observe_update sp_upd_map_empty disjoint_diff_pred)

text \<open>
If the non-updated and observed excerpts do not overlap only the updates can be observed.
\<close>

lemma sp_elem_map_diff_empty:
 "sp \<sqinter> (-sp') = \<bottom> \<Longrightarrow>
  sp_elem_map (sp-sp') a = Map.empty"
  apply(rule ext)
  apply(drule_tac x="(x,a!x)" in disjoint_pred)
  by(simp add: sp_elem_map iexcerpt_def)

lemma observe_update_only_update:
 "\<lbrakk>sp \<sqinter> (-sp') = \<bottom>\<rbrakk> \<Longrightarrow>
  sp_elem_map sp (spie_elem_upd sp' u a) = sp_upd_map sp sp' u a"
  by(simp add: observe_update sp_elem_map_diff_empty)

subsection \<open>Single Element Access Functions\<close>

text \<open>
Observation and update functions which access a single element.
\<close>

subsubsection \<open>Basic Access Functions\<close>

text \<open>
The basic access functions correspond to part access functions where every element is
a part. The parts are specified by their index.

The element observation function is derived from \<open>elem_map\<close>.
\<close>

definition elm :: "nat \<Rightarrow> 'el list \<Rightarrow> 'el"
  where "elm i a \<equiv> the (elem_map a i)"

lemma elm: "vld a i \<Longrightarrow> elm i a = nth a i"
  by(simp add: elm_def elem_map)

text \<open>
The element update function is derived from \<open>se_elem_upd\<close>, the new value only 
depends on the old value.
\<close>

definition elm_update :: "nat \<Rightarrow> ('el list, 'el) PartUpdate"
  where "elm_update i \<equiv> se_elem_upd (isingl i)"

lemma prsvelmsp_elm_update [lstp]: 
 "prsvp p u \<Longrightarrow> prsvelmsp p (elm_update i u)"
  by(simp add: elm_update_def lstp)
interpretation Prsvlstp_elm_update: Prsvlstp "elm_update i u"
  by(unfold_locales,simp add: elm_update_def lstp)

lemma elm_update: "vld a i \<Longrightarrow> elm_update i u = (\<lambda>a. list_update a i (u (nth a i)))"
  apply(simp add: elm_update_def se_elem_upd isingl)
  apply(rule ext)
  by(rule nth_equalityI,simp_all)

lemma elm_update_const: 
 "elm_update i (\<lambda>_. v) = s_elem_upd (isingl i) v"
  by(simp add: elm_update_def se_elem_upd_def s_elem_upd_def)

text \<open>
The single element access functions satisfy the part access laws for part access
functions with an additional argument.
\<close>

interpretation ElmAccess: ArgPartAccess vld elm elm_update
  apply(unfold_locales)
      apply(unfold elm_def elm_update_def se_elem_upd isingl elem_map)
      apply(rule nth_equalityI,simp,simp)
     apply(simp)
    apply(rule ext, simp add: map_nth)
   by(simp_all)

lemma elm_commUpd_elm[commUpd]: "i < j \<Longrightarrow> (elm_update j m2) \<circ> (elm_update i m1) = (elm_update i m1) \<circ> (elm_update j m2)"
  apply(rule ext)
  by(simp add: elm_update_def se_elem_upd isingl)

text \<open>Generalized Access: Element-wise Copying an Array\<close>

lemma i_elem_upd_copy:
 "length a1 = length a2 \<Longrightarrow>
  i_elem_upd (\<lambda>i. elm i a2) a1 = a2"
  apply(simp add: i_elem_upd)
  by(rule nth_equalityI,simp_all add: elm)

subsubsection \<open>Index Dependent Update\<close>

text \<open>
Define extended element update functions where the new value depends (only or also) on
the element index.
\<close>
definition elm_iupdate :: "nat \<Rightarrow> (nat \<Rightarrow> 'el) \<Rightarrow> 'el list \<Rightarrow> 'el list"
  where "elm_iupdate i \<equiv> si_elem_upd (isingl i)"

definition elm_ieupdate :: "nat \<Rightarrow> (nat \<times> 'el \<Rightarrow> 'el) \<Rightarrow> 'el list \<Rightarrow> 'el list"
  where "elm_ieupdate i \<equiv> sie_elem_upd (isingl i)"

lemma prsvelmsp_elm_iupdate [lstp]: 
 "p (u i) \<Longrightarrow> prsvelmsp p (elm_iupdate i u)"
  by(simp add: elm_iupdate_def prsvp_def elmsp_def si_elem_upd isingl)
interpretation Prsvlstp_elm_iupdate: Prsvlstp "elm_iupdate i u"
  by(unfold_locales,simp add: elm_iupdate_def lstp)
lemma prsvelmsp_elm_ieupdate [lstp]: 
 "prsvp p (\<lambda>x. u (i,x)) \<Longrightarrow> prsvelmsp p (elm_ieupdate i u)"
  by(simp add: elm_ieupdate_def prsvp_def elmsp_def sie_elem_upd isingl)
interpretation Prsvlstp_elm_ieupdate: Prsvlstp "elm_ieupdate i u"
  by(unfold_locales,simp add: elm_ieupdate_def lstp)

text \<open>
The standalone definitions are specified relative to \<open>elm\<close> and \<open>elm_update\<close>.
\<close>
lemma elm_iupdate:
 "elm_iupdate i u = elm_update i (\<lambda>_.u i)"
  apply(simp add: elm_update_def elm_iupdate_def se_elem_upd_def si_elem_upd_def spie_elem_upd)
  by(rule ext,simp add: split_def isingl)

lemma elm_ieupdate:
 "elm_ieupdate i u = elm_update i (curry u i)"
  by(auto simp add: elm_update_def elm_ieupdate_def se_elem_upd sie_elem_upd isingl)

text \<open>
Reversed conversion lemma for easy direct substitution.
\<close>
lemma elm_update_ieupdate:
 "elm_update i (u i) = elm_ieupdate i (case_prod u)"
  by(simp add: elm_ieupdate)

subsubsection \<open>Access Combined with a Predicate\<close>

text \<open>
Single element access functions with a guard predicate. The element is specified by a pair
of an index and an element predicate. The observation function returns an optional value.
For the update functions the new value depends only on the old value, only on the index,
or both.
\<close>

definition pelm :: "nat \<times> ('el \<Rightarrow> bool) \<Rightarrow> 'el list \<rightharpoonup> 'el"
  where "pelm ip a \<equiv> p_elem_map (snd ip) a (fst ip)"

definition pelm_update :: "nat \<times> ('el \<Rightarrow> bool) \<Rightarrow> ('el \<Rightarrow> 'el) \<Rightarrow> 'el list \<Rightarrow> 'el list"
  where "pelm_update ip \<equiv> spe_elem_upd (psingl ip)"

definition pelm_iupdate :: "nat \<times> ('el \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> 'el) \<Rightarrow> 'el list \<Rightarrow> 'el list"
  where "pelm_iupdate ip \<equiv> spi_elem_upd (psingl ip)"

definition pelm_ieupdate :: "nat \<times> ('el \<Rightarrow> bool) \<Rightarrow> (nat \<times> 'el \<Rightarrow> 'el) \<Rightarrow> 'el list \<Rightarrow> 'el list"
  where "pelm_ieupdate ip \<equiv> spie_elem_upd (psingl ip)"

lemma prsvelmsp_pelm_update [lstp]: 
 "prsvp p u \<Longrightarrow> prsvelmsp p (pelm_update ip u)"
  by(simp add: pelm_update_def lstp)
interpretation Prsvlstp_pelm_update: Prsvlstp "pelm_update ip u"
  by(unfold_locales,simp add: pelm_update_def lstp)
lemma prsvelmsp_pelm_iupdate [lstp]: 
 "p (u (fst ip)) \<Longrightarrow> prsvelmsp p (pelm_iupdate ip u)"
  by(simp add: pelm_iupdate_def prsvp_def elmsp_def spi_elem_upd psingl)
interpretation Prsvlstp_pelm_iupdate: Prsvlstp "pelm_iupdate ip u"
  by(unfold_locales,simp add: pelm_iupdate_def lstp)
lemma prsvelmsp_pelm_ieupdate [lstp]: 
 "prsvp p (\<lambda>x. u (fst ip,x)) \<Longrightarrow> prsvelmsp p (pelm_ieupdate ip u)"
  by(simp add: pelm_ieupdate_def prsvp_def elmsp_def spie_elem_upd psingl)
interpretation Prsvlstp_pelm_ieupdate: Prsvlstp "pelm_ieupdate ip u"
  by(unfold_locales,simp add: pelm_ieupdate_def lstp)

text \<open>
The standalone definitions are specified relative to \<open>elm\<close> and \<open>elm_update\<close>.
\<close>
lemma pelm:
 "vld a i \<Longrightarrow> pelm (i,p) a = (if p (elm i a) then Some (elm i a) else None)"
  by(simp add: pelm_def p_elem_map iexcerpt_def elm)
lemma pelm_update: 
 "vld a i \<Longrightarrow> 
  pelm_update (i,p) u a = 
  (if p (elm i a) then elm_update i u a else a)"
  apply(auto simp add: pelm_update_def spe_elem_upd psingl elm elm_update)
  apply(rule nth_equalityI,simp_all)
  by(rule nth_equalityI,auto)
lemma pelm_iupdate:
 "vld a i \<Longrightarrow>
  pelm_iupdate (i,p) u a = 
  (if p (elm i a) then elm_update i (\<lambda>_.u i) a else a)"
  apply(auto simp add: pelm_iupdate_def spi_elem_upd psingl elm elm_update)
  apply(rule nth_equalityI,simp_all)
  by(rule nth_equalityI,auto)
lemma pelm_ieupdate:
 "vld a i \<Longrightarrow>
  pelm_ieupdate (i,p) u a = 
  (if p (elm i a) then elm_update i (curry u i) a else a)"
  apply(auto simp add: pelm_ieupdate_def spie_elem_upd psingl elm elm_update)
  apply(rule nth_equalityI,simp_all)
  by(rule nth_equalityI,auto)

text \<open>
Reversed conversion lemma for easy direct substitution. Use together with \<open>pelm_update[symmetric]\<close>.
\<close>
lemma pelm_update_ieupdate:
 "pelm_update (i,p) (u i) = 
  pelm_ieupdate (i,p) (case_prod u)"
  apply(simp add: pelm_update_def pelm_ieupdate_def spe_elem_upd_def spie_elem_upd)
  by(rule ext,auto simp add: psingl)

subsection \<open>Iteration Support\<close>

text \<open>
When a loop iterates over an array it observes or modifies a growing excerpt, so the loop semantics
can be specified by an observation or modification of an excerpt. The proof is by induction and requires
to prove the semantics for the empty excerpt and for the step from an excerpt to a larger excerpt.
Finally, if the loop covers the whole array, the observation or modification can be proved for the 
array.

The simplest and most common case is a loop which iterates in steps of \<open>1\<close> starting at \<open>0\<close>. Here the
growing excerpt is an array prefix. The following laws can be used for induction proofs for
this case and are also intended as examples how to derive similar laws for other iteration schemes.

The laws are usually specified with and without an additional filter on the observed/modified elements.
\<close>

subsubsection \<open>Counting Elements\<close>

text \<open>
In every iteration the loop increments a counter. This is represented using \<open>sp_indx_num\<close>.
\<close>

text \<open>
Semantics for a single element.
\<close>
lemma isingl_indx_num:
 "vld a i \<Longrightarrow> s_indx_num (isingl i) a = 1"
  apply(simp add: s_indx_num isingl)
  apply(subst card_empty[symmetric])
  apply(subst card_insert_disjoint[where x=i,symmetric],simp,simp)
  by(rule_tac f=card in arg_cong,auto)
lemma psingl_indx_num:
 "vld a i \<Longrightarrow> sp_indx_num (psingl (i,p)) a = (if p (nth a i) then 1 else 0)"
  apply(simp add: sp_indx_num psingl iexcerpt_def)
  apply(rule)
  apply(subst card_empty[symmetric])
  apply(subst card_insert_disjoint[where x=i,symmetric],simp,simp)
  by(rule_tac f=card in arg_cong,auto)

text \<open>
Induction start: the empty prefix contains 0 elements.
\<close>
lemma iprefx_indx_num_start:
 "s_indx_num (iprefx 0) a = 0"
  by(simp add: iprefx s_indx_num iexcerpt_def)
lemma pprefx_indx_num_start:
 "sp_indx_num (pprefx (0,p)) a = 0"
  by(simp add: pprefx sp_indx_num iexcerpt_def)

text \<open>
Induction step: the successor prefix contains the sum of the prefix and the successor element.
\<close>
lemma iprefx_indx_num_step:
 "(s_indx_num (isingl i) a) + (s_indx_num (iprefx i) a) =
  s_indx_num (iprefx (Suc i)) a"
  apply(subst s_indx_num_S_union[symmetric])
   apply(auto simp add: isingl iprefx)[1]
  by(simp add: isingl_iprefx)
lemma pprefx_indx_num_step:
 "(sp_indx_num (psingl (i,p)) a) + (sp_indx_num (pprefx (i,p)) a) =
  sp_indx_num (pprefx (Suc i, p)) a"
  apply(subst sp_indx_num_SP_union[symmetric])
   apply(auto simp add: psingl pprefx)[1]
  by(simp add: psingl_pprefx)

text \<open>
A prefix up to the array length covers the whole array.
\<close>
lemma iprefx_indx_num_all:
 "i = length a \<Longrightarrow>
  s_indx_num (iprefx i) a = 
  indx_num a"
  apply(rule s_to_indx_num)
  by(simp add: iprefx)
lemma pprefx_indx_num_all:
 "i = length a \<Longrightarrow>
  sp_indx_num (pprefx (i, p)) a = 
  p_indx_num p a"
  apply(rule sp_to_p_indx_num)
  by(simp add: pprefx)

subsubsection \<open>Searching Elements\<close>

text \<open>
In every iteration the loop inspects one element. It returns the (optional) index of the 
first element satisfying a given predicate \<open>p\<close>. This is represented using \<open>sp_indx_fst\<close>.
\<close>

text \<open>
Semantics for a single element.
\<close>
lemma psingl_indx_fst:
 "vld a i \<Longrightarrow> sp_indx_fst (psingl (i,p)) a = (if p (nth a i) then Some i else None)"
  apply(simp add: sp_indx_fst psingl iexcerpt_def)
  by(rule impI,rule Least_equality,simp_all)

text \<open>
Induction start: the empty prefix cannot contain a matching element.
\<close>
lemma pprefx_indx_fst_start:
 "sp_indx_fst (pprefx (0,p)) a = None"
  by(simp add: pprefx sp_indx_fst iexcerpt_def)

text \<open>
Induction step: the result of the successor prefix is the result of the prefix, if found there,
otherwise the result of the successor match.
\<close>
lemma pprefx_indx_fst_step:
 "sp_indx_fst (pprefx (Suc i, p)) a =
  (if sp_indx_fst (pprefx (i,p)) a = None 
  then (sp_indx_fst (psingl (i,p)) a)
  else sp_indx_fst (pprefx (i,p)) a)"
  apply(subst psingl_pprefx[symmetric])
  apply(auto simp add: sp_indx_fst_SP_union)
  apply(case_tac "sp_indx_fst (psingl (i, p)) a",simp_all)
  apply(drule sp_indx_fst_satisfies_sp)+
  by(auto simp add: pprefx psingl)

text \<open>
A prefix up to the array length covers the whole array.
\<close>
lemma pprefx_indx_fst_all:
 "i = length a \<Longrightarrow>
  sp_indx_fst (pprefx (i, p)) a = 
  p_indx_fst p a"
  apply(rule sp_to_p_indx_fst)
  by(simp add: pprefx)

text \<open>
Searching with a parameter for a relation \<open>r\<close> is represented using \<open>sr_indx_fst_map\<close>.
\<close>

text \<open>
Semantics for a single element.
\<close>
lemma rsingl_indx_fst_map:
 "vld a i \<Longrightarrow> sr_indx_fst_map (rsingl (i,r)) a = (\<lambda>x. if r x (nth a i) then Some i else None)"
  apply(simp add: sr_indx_fst_map_def rsingl sp_indx_fst iexcerpt_def)
  apply(rule ext,auto simp add: iexcerpt_def)
  by(rule Least_equality,simp_all)

text \<open>
Induction start: the empty prefix cannot contain a matching element.
\<close>
lemma rprefx_indx_fst_map_start:
 "sr_indx_fst_map (rprefx (0,r)) a x = None"
  by(simp add: sr_indx_fst_map_def rprefx_pprefx pprefx_indx_fst_start)

text \<open>
Induction step: the result of the successor prefix is the result of the prefix, if found there,
otherwise the result of the successor match.
\<close>
lemma rprefx_indx_fst_map_step:
 "sr_indx_fst_map (rprefx (Suc i, r)) a x =
  (if sr_indx_fst_map (rprefx (i,r)) a x = None 
  then sr_indx_fst_map (rsingl (i,r)) a x
  else sr_indx_fst_map (rprefx (i,r)) a x)"
  apply(unfold sr_indx_fst_map_def)
  apply(simp add: rprefx_pprefx rsingl_psingl)
  by(simp add: pprefx_indx_fst_step)

text \<open>
A prefix up to the array length covers the whole array.
\<close>
lemma rprefx_indx_fst_map_all:
 "i = length a \<Longrightarrow>
  sr_indx_fst_map (rprefx (i, r)) a = 
  r_indx_fst_map r a"
  apply(unfold sr_indx_fst_map_def r_indx_fst_map_def)
  apply(rule ext)
  apply(simp add: rprefx_pprefx pprefx_indx_fst_all)
  apply(rule sp_to_p_indx_fst[symmetric])
  by(simp)

subsubsection \<open>Modifying an Array\<close>

text \<open>
In every iteration the loop updates a single element. 
\<close>

text \<open>
The semantics for a single element can be derived by folding the definition of the 
corresponding single element update function (\<open>elm_update\<close>, \<open>elm_iupdate\<close>, \<open>pelm_update\<close>, ...)
and applying its semantics.
\<close>

text \<open>
Induction start: updating the empty prefix is a no-op.
\<close>
lemma spie_elem_upd_start:
 "spie_elem_upd (pprefx (0,p)) u = id"
  by(rule ext, simp add: upd_bot pprefx_bot)
lemma spi_elem_upd_start:
 "spi_elem_upd (pprefx (0,p)) u = id"
  by(rule ext, simp add: upd_bot pprefx_bot)
lemma spe_elem_upd_start:
 "spe_elem_upd (pprefx (0,p)) u = id"
  by(rule ext, simp add: upd_bot pprefx_bot)
lemma sp_elem_upd_start:
 "sp_elem_upd (pprefx (0,p)) v = id"
  by(rule ext, simp add: upd_bot pprefx_bot)
lemma sie_elem_upd_start:
 "sie_elem_upd (iprefx 0) u = id"
  by(rule ext, simp add: upd_bot iprefx_bot)
lemma si_elem_upd_start:
 "si_elem_upd (iprefx 0) u = id"
  by(rule ext, simp add: upd_bot iprefx_bot)
lemma se_elem_upd_start:
 "se_elem_upd (iprefx 0) u = id"
  by(rule ext, simp add: upd_bot iprefx_bot)
lemma s_elem_upd_start:
 "s_elem_upd (iprefx 0) v = id"
  by(rule ext, simp add: upd_bot iprefx_bot)

text \<open>
Induction step: Updating a prefix and the successor element updates the successor prefix.
\<close>

lemma spie_elem_upd_step:
 "spie_elem_upd (psingl (i,p)) u (spie_elem_upd (pprefx (i,p)) u a) = 
  spie_elem_upd (pprefx (Suc i, p)) u a"
  apply(simp add: psingl_pprefx[symmetric])
  apply(rule upd_union)
  by(auto simp add: psingl pprefx comp_snd_def)
lemma spi_elem_upd_step:
 "spi_elem_upd (psingl (i,p)) u (spi_elem_upd (pprefx (i,p)) u a) = 
  spi_elem_upd (pprefx (Suc i, p)) u a"
  apply(simp add: psingl_pprefx[symmetric])
  by(rule upd_union)
lemma spe_elem_upd_step:
 "spe_elem_upd (psingl (i,p)) u (spe_elem_upd (pprefx (i,p)) u a) = 
  spe_elem_upd (pprefx (Suc i, p)) u a"
  apply(simp add: psingl_pprefx[symmetric])
  apply(rule upd_union)
  by(auto simp add: psingl pprefx comp_snd_def)
lemma sp_elem_upd_step:
 "sp_elem_upd (psingl (i,p)) u (sp_elem_upd (pprefx (i,p)) u a) = 
  sp_elem_upd (pprefx (Suc i, p)) u a"
  apply(simp add: psingl_pprefx[symmetric])
  by(rule upd_union)
lemma sie_elem_upd_step:
 "sie_elem_upd (isingl i) u (sie_elem_upd (iprefx i) u a) = 
  sie_elem_upd (iprefx (Suc i)) u a"
  apply(simp add: isingl_iprefx[symmetric])
  apply(rule upd_union)
  by(auto simp add: isingl iprefx comp_snd_def)
lemma si_elem_upd_step:
 "si_elem_upd (isingl i) u (si_elem_upd (iprefx i) u a) = 
  si_elem_upd (iprefx (Suc i)) u a"
  apply(simp add: isingl_iprefx[symmetric])
  by(rule upd_union)
lemma se_elem_upd_step:
 "se_elem_upd (isingl i) u (se_elem_upd (iprefx i) u a) = 
  se_elem_upd (iprefx (Suc i)) u a"
  apply(simp add: isingl_iprefx[symmetric])
  apply(rule upd_union)
  by(auto simp add: isingl iprefx comp_snd_def)
lemma s_elem_upd_step:
 "s_elem_upd (isingl i) u (s_elem_upd (iprefx i) u a) = 
  s_elem_upd (iprefx (Suc i)) u a"
  apply(simp add: isingl_iprefx[symmetric])
  by(rule upd_union)

text \<open>
A prefix up to the array length covers the whole array.
\<close>

lemma spie_elem_upd_all:
 "\<lbrakk>fst ip = length a; snd ip = p\<rbrakk> \<Longrightarrow>
  spie_elem_upd (pprefx ip) u a = 
  pie_elem_upd p u a"
  apply(rule sp_to_p_ie_elem_upd)
  by(simp add: pprefx)
lemma spi_elem_upd_all:
 "\<lbrakk>fst ip = length a; snd ip = p\<rbrakk> \<Longrightarrow>
  spi_elem_upd (pprefx ip) u a = 
  pi_elem_upd p u a"
  apply(rule sp_to_p_i_elem_upd)
  by(simp add: pprefx)
lemma spe_elem_upd_all:
 "\<lbrakk>fst ip = length a; snd ip = p\<rbrakk> \<Longrightarrow>
  spe_elem_upd (pprefx ip) u a = 
  pe_elem_upd p u a"
  apply(rule sp_to_p_e_elem_upd)
  by(simp add: pprefx)
lemma sp_elem_upd_all:
 "\<lbrakk>fst ip = length a; snd ip = p\<rbrakk> \<Longrightarrow>
  sp_elem_upd (pprefx ip) u a = 
  p_elem_upd p u a"
  apply(rule sp_to_p_elem_upd)
  by(simp add: pprefx)
lemma sie_elem_upd_all:
 "i = length a \<Longrightarrow>
  sie_elem_upd (iprefx i) u a = 
  ie_elem_upd u a"
  apply(rule s_to_ie_elem_upd)
  by(simp add: iprefx)
lemma si_elem_upd_all:
 "i = length a \<Longrightarrow>
  si_elem_upd (iprefx i) u a = 
  i_elem_upd u a"
  apply(rule s_to_i_elem_upd)
  by(simp add: iprefx)
lemma se_elem_upd_all:
 "i = length a \<Longrightarrow>
  se_elem_upd (iprefx i) u a = 
  e_elem_upd u a"
  apply(rule s_to_e_elem_upd)
  by(simp add: iprefx)
lemma s_elem_upd_all:
 "i = length a \<Longrightarrow>
  s_elem_upd (iprefx i) u a = 
  elem_upd u a"
  apply(rule s_to_elem_upd)
  by(simp add: iprefx)

subsubsection \<open>Comparing two Arrays\<close>

text \<open>
The loop compares two arrays element-wise. As long as the elements are equal the prefixes
are equal. When elements differ the prefixes differ and the loop can stop, because this implies
that all larger prefixes differ as well.
\<close>

text \<open>
If elements are equal then the singleton maps are equal.
\<close>
lemma elm_eq_isingl_map_eq:
 "\<lbrakk>vld a i; vld b i\<rbrakk> \<Longrightarrow> 
  elm i a = elm i b \<longleftrightarrow>
  s_elem_map (isingl i) a = s_elem_map (isingl i) b"
  apply(auto simp add: elm_def s_eq_elem_map iexcerpt_def isingl elem_map s_elem_map)
  by(drule_tac x=i in fun_cong,auto)
lemma elm_eq_psingl_map_eq:
 "\<lbrakk>vld a i; vld b i\<rbrakk> \<Longrightarrow>
  elm i a = elm i b \<or> (\<not> p (elm i a) \<and> \<not> p (elm i b)) \<longrightarrow>
  sp_elem_map (psingl (i,p)) a = sp_elem_map (psingl (i,p)) b"
  apply(auto simp add: elm_def sp_eq_elem_map iexcerpt_def psingl elem_map sp_elem_map)
  by(rule ext,auto)

text \<open>
Induction start: empty prefixes are always equal.
\<close>
lemma iprefx_elem_map_eq_start:
 "s_elem_map (iprefx 0) a = s_elem_map (iprefx 0) b"
  by(simp add: s_elem_map_S_bot iprefx_bot)
lemma pprefx_elem_map_eq_start:
 "sp_elem_map (pprefx (0,p)) a = sp_elem_map (pprefx (0,p)) b"
  by(simp add: sp_elem_map_SP_bot pprefx_bot)

text \<open>
Induction step: Successor prefixes are equal if prefixes are equal and successor elements are equal.
\<close>
lemma iprefx_elem_map_eq_step:
 "s_elem_map (iprefx (Suc i)) a = s_elem_map (iprefx (Suc i)) b \<longleftrightarrow>
  (s_elem_map (isingl i) a = s_elem_map (isingl i) b \<and>
  s_elem_map (iprefx i) a = s_elem_map (iprefx i) b)"
  apply(simp add: isingl_iprefx[symmetric] s_elem_map_S_union)
  by (metis (full_types) s_elem_map_S_le_cong s_elem_map_S_union sup.cobounded1 sup.cobounded2)
lemma pprefx_elem_map_eq_step:
 "sp_elem_map (pprefx (Suc i,p)) a = sp_elem_map (pprefx (Suc i,p)) b \<longleftrightarrow>
  (sp_elem_map (psingl (i,p)) a = sp_elem_map (psingl (i,p)) b \<and>
  sp_elem_map (pprefx (i,p)) a = sp_elem_map (pprefx (i,p)) b)"
  apply(simp add: psingl_pprefx[symmetric] sp_elem_map_SP_union)
  by (smt sp_elem_map_SP_le_cong sp_elem_map_SP_union sup.cobounded1 sup.cobounded2)

text \<open>
A prefix up to the array length covers the whole array.
\<close>
lemma iprefx_elem_map_eq_all:
 "\<lbrakk>length a = length b; s_elem_map (iprefx (length a)) a = s_elem_map (iprefx (length b)) b\<rbrakk> \<Longrightarrow>
  elem_map a = elem_map b"
  apply(subst s_to_elem_map[symmetric,where s="iprefx (length a)"])
  apply(simp add: iprefx_def islice_def)
  apply(subst s_to_elem_map[symmetric,where s="iprefx (length b)"])
   apply(simp add: iprefx_def islice_def)
  by(simp)
lemma pprefx_elem_map_eq_all:
 "\<lbrakk>i = length a; i = length b; sp_elem_map (pprefx (i,p)) a = sp_elem_map (pprefx (i,p)) b\<rbrakk> \<Longrightarrow>
  p_elem_map p a = p_elem_map p b"
  apply(subst sp_to_p_elem_map[symmetric,where sp="pprefx (i,p)"])
  apply(simp add:pprefx_def iprefx_def islice_def)
  apply(subst sp_to_p_elem_map[symmetric,where sp="pprefx (i,p)"])
   apply(simp add:pprefx_def iprefx_def islice_def)
  by(simp)

end
