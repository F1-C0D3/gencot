
theory Gencot_ArrayBaseSupport
  imports Gencot_MapSupport
  "HOL-Library.Adhoc_Overloading"
  Gencot_PartAccessSupport
begin

subsection \<open>Predicates and Relations\<close>

(* These notations are removed in Main.thy, reactivate them. *)
notation
  bot ("\<bottom>") and top ("\<top>") and
  inf (infixl "\<sqinter>" 70) and sup (infixl "\<squnion>" 65) and
  Inf ("\<Sqinter>") and Sup ("\<Squnion>")

definition comp_snd :: "('a \<times> 'b \<Rightarrow> 'c) \<Rightarrow> ('a \<times> 'd \<Rightarrow> 'b) \<Rightarrow> ('a \<times> 'd \<Rightarrow> 'c)" (infixl "\<circ>\<^sub>2" 55)
  where "f \<circ>\<^sub>2 g \<equiv> \<lambda>(x,y). f (x,g(x,y))"

lemma top_pred: "(\<lambda>a. True) = \<top>" by auto
lemma bot_pred: "(\<lambda>a. False) = \<bottom>" by auto
lemma bot_rel: "(\<lambda>a b. False) = \<bottom>" by auto
lemma disjoint_pred: "sp1 \<sqinter> sp2 = \<bottom> \<Longrightarrow> (sp1 x \<and> sp2 x) = False"
  by (metis (full_types) bot_pred inf.idem inf_apply)
lemma disjoint_rel: "sp1 \<sqinter> sp2 = \<bottom> \<Longrightarrow> (sp1 x y \<and> sp2 x y) = False"
  by (metis bot_apply compl_bot_eq compl_inf_bot compl_top_eq disjoint_pred inf2I inf_compl_bot_left1)
lemma un_comp_pred: "sp1 \<squnion> sp2 \<circ> sp = (sp1 \<circ> sp) \<squnion> (sp2 \<circ> sp)" by auto
lemma disjoint_diff_pred: "sp1 \<sqinter> sp2 = \<bottom> \<Longrightarrow> (sp1 - sp2) = sp1" for sp1 :: "'a \<Rightarrow> bool"
  apply(rule ext)
  using disjoint_pred by fastforce
lemma neg_pred[simp]: "- p = (\<lambda>a. \<not> p a)"  by auto
lemma minus_pred: "p1 - p2 = (\<lambda>a. p1 a \<and> \<not> p2 a)" by(auto)
lemma pred_prod_top1: "pred_prod \<top> r = r\<circ>snd" by auto
lemma pred_prod_top2: "pred_prod r \<top> = r\<circ>fst" by auto
lemma le_pred: "(a \<le> b) = (\<forall>x. ((a x) \<longrightarrow> (b x)))" for a::"'a \<Rightarrow> bool" by(auto)
lemma le_rel: "(a \<le> b) = (\<forall>x y. ((a x y) \<longrightarrow> (b x y)))" for a::"'a \<Rightarrow> 'b \<Rightarrow> bool" by(auto)

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
lemma isingl_iprefx_bot:
 "(isingl im) \<sqinter> (iprefx im) = \<bottom>"
  by(auto simp add: iprefx_def isingl_def islice_def)

subsubsection \<open>Index based Excerpts with a predicate\<close>

text \<open>
The following functions combine index based excerpts with an element predicate.
\<close>

definition pexcrp :: "(nat \<Rightarrow> bool) \<times> ('el \<Rightarrow> bool) \<Rightarrow> nat \<times> 'el \<Rightarrow> bool"
  where "pexcrp sp \<equiv> pred_prod (fst sp) (snd sp)"
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
lemma psingl_pprefx_bot:
 "(psingl (i, p)) \<sqinter> (pprefx (i, p)) = \<bottom>"
  by(auto simp add: pprefx psingl)

subsubsection \<open>Index based Excerpts with a Relation\<close>

text \<open>
The following functions combine index based excerpts with a relation between
an additional parameter and an element. 
\<close>

definition rexcrp :: "(nat \<Rightarrow> bool) \<times> ('t \<Rightarrow> 'el \<Rightarrow> bool) \<Rightarrow> 't \<Rightarrow> nat \<times> 'el \<Rightarrow> bool"
  where "rexcrp sr \<equiv> \<lambda>x. pred_prod (fst sr) (snd sr x)"
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
lemma rsingl_rprefx_bot:
 "(rsingl (i, r)) \<sqinter> (rprefx (i, r)) = \<bottom>"
  by(auto simp add: rprefx rsingl)

text \<open>Abbreviation for combination of \<open>iexcerpt\<close> and \<open>rexcrp\<close>\<close>

definition rexcerpt :: "(nat \<Rightarrow> bool) \<times> ('t \<Rightarrow> 'el \<Rightarrow> bool) \<Rightarrow> 't \<Rightarrow> 'el list \<Rightarrow> nat \<Rightarrow> bool"
  where "rexcerpt sr x \<equiv> iexcerpt (rexcrp sr x)"

lemma rexcerpt: 
 "rexcerpt sr x a = (\<lambda>i. i < length a \<and> (fst sr) i \<and> (snd sr) x (a ! i))"
  by(simp add: rexcerpt_def iexcerpt_def rexcrp_def)

end
