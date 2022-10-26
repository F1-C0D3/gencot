section \<open>Array Support\<close>

theory Gencot_ArrayModifSupport
  imports Gencot_ArraySearchSupport
begin

subsection \<open>Modification Functions\<close>

subsubsection \<open>Property Preservation\<close>

text \<open>
All modification functions preserve the length of the list. This can be 
expressed by the following preservation property.
\<close>

abbreviation "prsvlen \<equiv> prsv length"

lemma prsvlen: "prsvlen u = (\<forall>x. length (u x) = length x)"
  by(auto simp add: prsv_def comp_def)

text \<open>
All modification functions also preserve arbitrary properties for the elements,
if the element update function preserves this property. This can be 
expressed using the following predicates.
\<close>

definition elmsp :: "('el \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> bool"
  where "elmsp p \<equiv> \<lambda>x. \<forall>i. vld x i \<longrightarrow> p (nth x i)"
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
lemma prsvlen_comp[simp]: "\<lbrakk>prsvlen u\<rbrakk> \<Longrightarrow> prsvlen (f \<circ> u)"
  using prsvlen apply(simp add: prsv_def)
  by (metis comp_assoc)
lemma prsvlen_appl[simp]: "\<lbrakk>prsvlen u\<rbrakk> \<Longrightarrow> prsvlen (\<lambda>x. f (u x))"
  using prsvlen by(simp add: prsv_def comp_def)
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
 "\<forall>i. (\<exists>e. sp (i,e)) \<longrightarrow> prsvp p (\<lambda>x. u (i,x)) \<Longrightarrow> prsvelmsp p (spie_elem_upd sp u)"
  apply(auto simp add: spie_elem_upd_def prsvp_def elmsp_def)
  by (metis mem_Collect_eq nth_enumerate_eq override_on_apply_in override_on_apply_notin sndI)

lemma
 "\<forall>i. prsvp p (\<lambda>x. u (i,x)) \<Longrightarrow> prsvelmsp p (spie_elem_upd sp u)"
  apply(auto simp add: spie_elem_upd_def prsvp_def elmsp_def)
  by (metis nth_enumerate_eq override_on_apply_in override_on_apply_notin snd_conv)
interpretation Prsvlstp_spie_elem_upd: Prsvlstp "spie_elem_upd sp u"
  by(unfold_locales,simp add: spie_elem_upd_def prsvlen)

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
 "\<forall>i. (\<exists>e. sp (i,e)) \<longrightarrow> p (u i) \<Longrightarrow> prsvelmsp p (spi_elem_upd sp u)"
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
 "\<forall>i. s(i) \<longrightarrow> prsvp p (\<lambda>x. u (i,x)) \<Longrightarrow> prsvelmsp p (sie_elem_upd s u)"
  by(simp add: sie_elem_upd_def lstp)
interpretation Prsvlstp_sie_elem_upd: Prsvlstp "sie_elem_upd s u"
  by(unfold_locales,simp add: sie_elem_upd_def lstp)
lemma prsvelmsp_si_elem_upd [lstp]: 
 "\<forall>i. s(i) \<longrightarrow> p (u i) \<Longrightarrow> prsvelmsp p (si_elem_upd s u)"
  apply(unfold si_elem_upd_def)
  apply(rule prsvelmsp_spie_elem_upd)
  by(simp add: prsvp_def)
interpretation Prsvlstp_si_elem_upd: Prsvlstp "si_elem_upd s u"
  by(unfold_locales,simp add: si_elem_upd_def lstp)
lemma prsvelmsp_se_elem_upd [lstp]: 
 "prsvp p u \<Longrightarrow> prsvelmsp p (se_elem_upd s u)"
  by(simp add: se_elem_upd_def lstp)
interpretation Prsvlstp_se_elem_upd: Prsvlstp "se_elem_upd s u"
  by(unfold_locales,simp add: se_elem_upd_def lstp)
lemma prsvelmsp_s_elem_upd [lstp]: 
 "p v \<Longrightarrow> prsvelmsp p (s_elem_upd s v)"
  apply(unfold s_elem_upd_def)
  apply(rule prsvelmsp_spie_elem_upd)
  by(simp add: prsvp_def)
interpretation Prsvlstp_s_elem_upd: Prsvlstp "s_elem_upd s u"
  by(unfold_locales,simp add: s_elem_upd_def lstp)
lemma prsvelmsp_pie_elem_upd [lstp]: 
 "\<forall>i. prsvp p (\<lambda>x. u (i,x)) \<Longrightarrow> prsvelmsp p (pie_elem_upd p' u)"
  by(auto simp add: pie_elem_upd_def lstp)
interpretation Prsvlstp_pie_elem_upd: Prsvlstp "pie_elem_upd p' u"
  by(unfold_locales,simp add: pie_elem_upd_def lstp)
lemma prsvelmsp_pi_elem_upd [lstp]: 
 "\<forall>i. p (u i) \<Longrightarrow> prsvelmsp p (pi_elem_upd p' u)"
  apply(unfold pi_elem_upd_def)
  apply(rule prsvelmsp_spie_elem_upd)
  by(simp add: prsvp_def)
interpretation Prsvlstp_pi_elem_upd: Prsvlstp "pi_elem_upd p' u"
  by(unfold_locales,simp add: pi_elem_upd_def lstp)
lemma prsvelmsp_pe_elem_upd [lstp]: 
 "prsvp p u \<Longrightarrow> prsvelmsp p (pe_elem_upd p' u)"
  by(simp add: pe_elem_upd_def lstp)
interpretation Prsvlstp_pe_elem_upd: Prsvlstp "pe_elem_upd p' u"
  by(unfold_locales,simp add: pe_elem_upd_def lstp)
lemma prsvelmsp_p_elem_upd [lstp]: 
 "p v \<Longrightarrow> prsvelmsp p (p_elem_upd p' v)"
  apply(unfold p_elem_upd_def)
  apply(rule prsvelmsp_spie_elem_upd)
  by(simp add: prsvp_def)
interpretation Prsvlstp_p_elem_upd: Prsvlstp "p_elem_upd p' u"
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
lemma spie_elem_upd_id: 
 "iexcerpt sp a = \<bottom> \<Longrightarrow> spie_elem_upd sp u a = a"
  apply(simp add: spie_elem_upd iexcerpt_def)
  apply(rule nth_equalityI,simp_all)
  by(drule_tac x=i in fun_cong,simp)
lemma spi_elem_upd_id: 
 "iexcerpt sp a = \<bottom> \<Longrightarrow> spi_elem_upd sp u a = a"
  by(simp add: spi_elem_upd_def spie_elem_upd_id)
lemma spe_elem_upd_id: 
 "iexcerpt sp a = \<bottom> \<Longrightarrow> spe_elem_upd sp u a = a"
  by(simp add: spe_elem_upd_def spie_elem_upd_id)
lemma sp_elem_upd_id: 
 "iexcerpt sp a = \<bottom> \<Longrightarrow> sp_elem_upd sp u a = a"
  by(simp add: sp_elem_upd_def spie_elem_upd_id)
lemma sie_elem_upd_id: 
 "\<forall>i. vld a i \<longrightarrow> \<not> s i \<Longrightarrow> sie_elem_upd s u a = a"
  apply(simp add: sie_elem_upd)
  by(rule nth_equalityI,simp_all)
lemma si_elem_upd_id: 
 "\<forall>i. vld a i \<longrightarrow> \<not> s i \<Longrightarrow> si_elem_upd s u a = a"
  by(simp add: si_elem_upd_def sie_elem_upd_def[symmetric] sie_elem_upd_id)
lemma se_elem_upd_id: 
 "\<forall>i. vld a i \<longrightarrow> \<not> s i \<Longrightarrow> se_elem_upd s u a = a"
  by(simp add: se_elem_upd_def sie_elem_upd_def[symmetric] sie_elem_upd_id)
lemma s_elem_upd_id: 
 "\<forall>i. vld a i \<longrightarrow> \<not> s i \<Longrightarrow> s_elem_upd s u a = a"
  by(simp add: s_elem_upd_def sie_elem_upd_def[symmetric] sie_elem_upd_id)
lemma pie_elem_upd_id: 
 "\<forall>i. vld a i \<longrightarrow> \<not> p (a!i) \<Longrightarrow> pie_elem_upd p u a = a"
  apply(simp add: pie_elem_upd)
  by(rule nth_equalityI,simp_all)
lemma pi_elem_upd_id: 
 "\<forall>i. vld a i \<longrightarrow> \<not> p (a!i) \<Longrightarrow> pi_elem_upd p u a = a"
  by(simp add: pi_elem_upd_def pie_elem_upd_def[symmetric] pie_elem_upd_id)
lemma pe_elem_upd_id: 
 "\<forall>i. vld a i \<longrightarrow> \<not> p (a!i) \<Longrightarrow> pe_elem_upd p u a = a"
  by(simp add: pe_elem_upd_def pie_elem_upd_def[symmetric] pie_elem_upd_id)
lemma p_elem_upd_id: 
 "\<forall>i. vld a i \<longrightarrow> \<not> p (a!i) \<Longrightarrow> p_elem_upd p u a = a"
  by(simp add: p_elem_upd_def pie_elem_upd_def[symmetric] pie_elem_upd_id)

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

subsubsection \<open>Overwriting Updates\<close>

text \<open>
If an update does not depend on the existing elements, it overwrites any previous update
in every sub excerpt.
\<close>
lemma si_elem_upd_overwrite:
 "sp' \<le> s\<circ>fst \<Longrightarrow>
  si_elem_upd s u (spie_elem_upd sp' u' g) = si_elem_upd s u g"
  apply(simp add: si_elem_upd spie_elem_upd)
  by(auto)
lemma s_elem_upd_overwrite:
 "sp' \<le> s\<circ>fst \<Longrightarrow>
  s_elem_upd s v (spie_elem_upd sp' u' g) = s_elem_upd s v g"
  apply(simp add: s_elem_upd spie_elem_upd)
  by(auto)
lemma i_elem_upd_overwrite:
 "i_elem_upd u (spie_elem_upd sp' u' g) = i_elem_upd u g"
  by(simp add: i_elem_upd spie_elem_upd)
lemma elem_upd_overwrite:
 "elem_upd v (spie_elem_upd sp' u' g) = elem_upd v g"
  by(simp add: elem_upd spie_elem_upd)

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
  where "sp_upd sp u \<equiv> \<lambda>(i,e). \<exists>e'. e = u (i,e') \<and> sp (i,e')"

definition sp_app :: "(nat \<times> 'el \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> (nat \<times> 'el \<Rightarrow> bool)"
  where "sp_app sp a \<equiv> \<lambda>(i,_). sp (i, nth a i)"
definition sp_dis :: "(nat \<times> 'el \<Rightarrow> bool) \<Rightarrow> (nat \<times> 'el \<Rightarrow> bool) \<Rightarrow> 'el list \<Rightarrow> bool"
  where "sp_dis sp1 sp2 a \<equiv> \<forall>i. \<not> (iexcerpt sp1 a i \<and> iexcerpt sp2 a i)"

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

lemma sp_upd_map':
 "sp_upd_map sp sp' u a =
  (\<lambda>i. if iexcerpt sp' a i \<and> sp (i, u(i,a!i)) then Some (u(i,a!i)) else None )"
  apply(simp add: sp_upd_map sp_elem_map iexcerpt_def make_iemap update_iemap_def map_comp_def comp_snd_def)
  apply(rule ext)
  apply(case_tac "k < length a \<and> sp' (k, a ! k)")
  by(auto simp add: sp_restrict_iemap_def from_iemap_def)

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

lemma disjoint_dom_sp_elem_upd_map:
 "dom (sp_elem_map (sp-sp') a) \<inter> dom (sp_upd_map sp sp' u a) = {}"
  apply(simp add: dom_sp_elem_map_diff dom_sp_upd_map)
  apply(fold sp_indx_set_def)
  by(auto simp add: sp_indx_set iexcerpt_def)

theorem sp_observe_update:
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
   apply(insert disjoint_dom_sp_elem_upd_map)[1]
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

lemma sp_upd_map_empty':
 "sp_dis sp sp' a \<Longrightarrow>
  sp_upd_map (sp_app sp a) sp' u a = Map.empty"
  apply(simp add: sp_upd_map sp_dis_def sp_app_def)
  apply(rule ext)
  apply(simp add: map_comp_def from_iemap_def sp_restrict_iemap_def update_iemap_def make_iemap)
  by(auto simp add: comp_snd_def sp_elem_map iexcerpt_def restrict_map_def)

lemma sp_observe_update_no_update:
 "\<lbrakk>sp \<sqinter> sp' = \<bottom>; sp \<sqinter> sp_upd sp' u = \<bottom>\<rbrakk> \<Longrightarrow>
  sp_elem_map sp (spie_elem_upd sp' u a) = sp_elem_map sp a"
  by(simp add: sp_observe_update sp_upd_map_empty disjoint_diff_pred)

lemma sp_observe_update_no_update':
 "\<lbrakk>sp_dis sp sp' a\<rbrakk> \<Longrightarrow>
  sp_elem_map (sp_app sp a) (spie_elem_upd sp' u a) = sp_elem_map sp a"
  apply(simp add: sp_observe_update sp_upd_map_empty' disjoint_diff_pred)
  apply(rule ext)
  by(simp add: sp_elem_map iexcerpt_def sp_app_def sp_dis_def)

text \<open>
If the non-updated and observed excerpts do not overlap only the updates can be observed.
\<close>

lemma sp_elem_map_diff_empty:
 "sp \<sqinter> (-sp') = \<bottom> \<Longrightarrow>
  sp_elem_map (sp-sp') a = Map.empty"
  apply(rule ext)
  apply(drule_tac x="(x,a!x)" in disjoint_pred)
  by(simp add: sp_elem_map iexcerpt_def)

lemma sp_elem_map_diff_empty':
 "sp_dis sp (-sp') a \<Longrightarrow>
  sp_elem_map (sp_app sp a - sp') a = Map.empty"
  apply(rule ext)
  by(simp add: sp_dis_def sp_elem_map iexcerpt_def sp_app_def)

lemma sp_observe_update_only_update:
 "\<lbrakk>sp \<sqinter> (-sp') = \<bottom>\<rbrakk> \<Longrightarrow>
  sp_elem_map sp (spie_elem_upd sp' u a) = sp_upd_map sp sp' u a"
  by(simp add: sp_observe_update sp_elem_map_diff_empty)

lemma sp_observe_update_only_update':
 "\<lbrakk>sp_dis sp'' (-sp') a; sp = (sp_app sp'' a)\<rbrakk> \<Longrightarrow>
  sp_elem_map sp (spie_elem_upd sp' u a) = sp_upd_map sp sp' u a"
  by(simp add: sp_observe_update sp_elem_map_diff_empty')

text \<open>
If an update is observed in an excerpt, the update can be reduced to that excerpt.
This is only possible for index based excerpts. For an element based excerpt it is in general not
possible to distinguish updated and non-updated elements by an element property alone.
For the special case of searching with \<open>sr_indx_fst_map\<close> a similar rule is possible because 
the index excerpt is a separate part of the excerpt pair, the same holds for other \<open>sr\<close> functions.
\<close>

lemma s_observe_update_restrict:
 "s_elem_map s (spie_elem_upd sp u a) = s_elem_map s (spie_elem_upd (sp \<sqinter> (s\<circ>fst)) u a)"
  apply(simp add: s_elem_map_def sp_observe_update)
  apply(subgoal_tac "((s \<circ> fst) - sp) = ((s \<circ> fst) - sp \<sqinter> (s \<circ> fst))",erule ssubst)
  apply(simp add: sp_upd_map' iexcerpt_def)
  by(rule ext,auto)

lemma sr_observe_update_restrict:
 "sr_indx_fst_map sr (spie_elem_upd sp u a) = sr_indx_fst_map sr (spie_elem_upd (sp \<sqinter> ((prod.fst sr)\<circ>prod.fst)) u a)"
  apply(rule ext)
  apply(simp add: sr_indx_fst_map_def sp_indx_fst_def sp_indx_set_def)
  apply(simp add: sp_observe_update)
  apply(subgoal_tac "(rexcrp sr x - sp) = (rexcrp sr x - sp \<sqinter> (fst sr \<circ> fst))",erule ssubst)
  apply(simp add: sp_upd_map' iexcerpt_def rexcrp_def)
  by(rule ext,auto simp add:rexcrp_def)

lemma sr_injective_update_restrict:
 "sr_injective sr (spie_elem_upd sp u a) = sr_injective sr (spie_elem_upd (sp \<sqinter> ((prod.fst sr)\<circ>prod.fst)) u a)"
  by(auto simp add: sr_injective_def rexcerpt spie_elem_upd)

lemma sr_inv_observe_update_restrict:
 "sr_indx_all_inv sr (spie_elem_upd sp u a) = sr_indx_all_inv sr (spie_elem_upd (sp \<sqinter> ((prod.fst sr)\<circ>prod.fst)) u a)"
  apply(rule ext)
  by(auto simp add: sr_indx_all_inv_def iexcerpt_def sr_some_def rexcrp_def spie_elem_upd)

lemma sr_uniq_update_restrict:
 "sr_uniq sr (spie_elem_upd sp u a) = sr_uniq sr (spie_elem_upd (sp \<sqinter> ((prod.fst sr)\<circ>prod.fst)) u a)"
  by(auto simp add: sr_uniq_def sp_uniq_def rexcrp_def iexcerpt_def spie_elem_upd)

text \<open>Simplified forms\<close>

definition s_upd_map :: "(nat \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> (nat \<times> 'el \<Rightarrow> 'el) \<Rightarrow> 'el list \<Rightarrow> (nat \<rightharpoonup> 'el)"
  where "s_upd_map s s' u \<equiv> sp_upd_map (s\<circ>fst) (s'\<circ>fst) u"
definition p_upd_map :: "('el \<Rightarrow> bool) \<Rightarrow> ('el \<Rightarrow> bool) \<Rightarrow> (nat \<times> 'el \<Rightarrow> 'el) \<Rightarrow> 'el list \<Rightarrow> (nat \<rightharpoonup> 'el)"
  where "p_upd_map p p' u \<equiv> sp_upd_map (p\<circ>snd) (p'\<circ>snd) u"
definition upd_map :: "(nat \<times> 'el \<Rightarrow> 'el) \<Rightarrow> 'el list \<Rightarrow> (nat \<rightharpoonup> 'el)"
  where "upd_map u \<equiv> sp_upd_map \<top> \<top> u"

lemma s_upd_map':
 "s_upd_map s s' u a =
  (\<lambda>i. if vld a i \<and> s' i \<and> s i then Some (u(i,a!i)) else None)"
  by(simp add: s_upd_map_def sp_upd_map' iexcerpt_def)
lemma p_upd_map':
 "p_upd_map p p' u a =
  (\<lambda>i. if vld a i \<and> p' (a!i) \<and> p(u(i,a!i)) then Some (u(i,a!i)) else None)"
  by(simp add: p_upd_map_def sp_upd_map' iexcerpt_def)
lemma upd_map':
 "upd_map u a =
  (\<lambda>i. if vld a i then Some (u(i,a!i)) else None)"
  by(simp add: upd_map_def sp_upd_map' iexcerpt_def)

subsubsection \<open>Access Rules for Excerpts\<close>

text \<open>
An excerpt can be considered as a part of an array in the sense of theory \<open>Gencot_PartAccessSupport\<close>.
Then the type of a selector is an excerpt, the type of a part is a map, and the type of a whole is a list.
The part access function is \<open>sp_elem_map\<close> which retrieves the map for an excerpt, the part update function
is \<open>spie_elem_upd\<close> which modifies the excerpt. Instead of a part modification function it uses a 
restricted form which does not allow moving, adding, or removing entries.

The corresponding adapted part access rules for these functions and for their derived simpler forms are given here.
\<close>

lemma spie_elem_distUpd:
 "sp1 = sp_app sp2 a \<Longrightarrow>
  (spie_elem_upd sp1 u1 (spie_elem_upd sp2 u2 a)) = spie_elem_upd sp2 (u1 \<circ>\<^sub>2 u2) a"
  by(simp add: spie_elem_upd comp_snd_def sp_app_def)
lemma spi_elem_distUpd:
 "(spi_elem_upd (sp_app sp a) u1 (spi_elem_upd sp u2 a)) = spi_elem_upd sp u1 a"
  by(simp add: spi_elem_upd sp_app_def)
lemma spe_elem_distUpd:
 "(spe_elem_upd (sp_app sp a) u1 (spe_elem_upd sp u2 a)) = spe_elem_upd sp (u1 \<circ> u2) a"
  by(simp add: spe_elem_upd sp_app_def)
lemma sp_elem_distUpd:
 "(sp_elem_upd (sp_app sp a) v1 (sp_elem_upd sp v2 a)) = sp_elem_upd sp v1 a"
  by(simp add: sp_elem_upd sp_app_def)
lemma sie_elem_distUpd:
 "(sie_elem_upd s u1 (sie_elem_upd s u2 a)) = sie_elem_upd s (u1 \<circ>\<^sub>2 u2) a"
  by(simp add: sie_elem_upd comp_snd_def)
lemma si_elem_distUpd:
 "(si_elem_upd s u1 (si_elem_upd s u2 a)) = si_elem_upd s u1 a"
  by(simp add: si_elem_upd)
lemma se_elem_distUpd:
 "(se_elem_upd s u1 (se_elem_upd s u2 a)) = se_elem_upd s (u1 \<circ> u2) a"
  by(simp add: se_elem_upd)
lemma s_elem_distUpd:
 "(s_elem_upd s v1 (s_elem_upd s v2 a)) = s_elem_upd s v1 a"
  by(simp add: s_elem_upd)
(* No distUpd rules exist for pie/pi/pe/p_elem_upd *)
lemma ie_elem_distUpd:
 "(ie_elem_upd u1 (ie_elem_upd u2 a)) = ie_elem_upd (u1 \<circ>\<^sub>2 u2) a"
  by(simp add: ie_elem_upd comp_snd_def)
lemma i_elem_distUpd:
 "(i_elem_upd u1 (i_elem_upd u2 a)) = i_elem_upd u1 a"
  by(simp add: i_elem_upd)
lemma e_elem_distUpd:
 "(e_elem_upd u1 (e_elem_upd u2 a)) = e_elem_upd (u1 \<circ> u2) a"
  by(simp add: e_elem_upd)
lemma elem_distUpd:
 "(elem_upd v1 (elem_upd v2 a)) = elem_upd v1 a"
  by(simp add: elem_upd)

lemma spie_elem_identUpd:
 "spie_elem_upd sp snd = (\<lambda>a. a)"
  by(simp add: spie_elem_upd_def override_on_def)
lemma spi_elem_identUpd:
 "spi_elem_upd sp (nth a) a = a"
  by(simp add: spi_elem_upd map_nth)
lemma spe_elem_identUpd:
 "spe_elem_upd sp (\<lambda>a. a) = (\<lambda>a. a)"
  by(simp add: spe_elem_upd map_nth)
(* No identUpd rule exists for sp_elem_upd *)
lemma sie_elem_identUpd:
 "sie_elem_upd s snd = (\<lambda>a. a)"
  by(rule ext, simp add: sie_elem_upd,rule nth_equalityI,simp_all)
lemma si_elem_identUpd:
 "si_elem_upd s (nth a) a = a"
  by(simp add: si_elem_upd,rule nth_equalityI,simp_all)
lemma se_elem_identUpd:
 "se_elem_upd s (\<lambda>a. a) = (\<lambda>a. a)"
  by(rule ext, simp add: se_elem_upd,rule nth_equalityI,simp_all)
(* No identUpd rule exists for s_elem_upd *)
lemma pie_elem_identUpd:
 "pie_elem_upd p snd = (\<lambda>a. a)"
  by(rule ext, simp add: pie_elem_upd,rule nth_equalityI,simp_all)
lemma pi_elem_identUpd:
 "pi_elem_upd p (nth a) a = a"
  by(simp add: pi_elem_upd,rule nth_equalityI,simp_all)
lemma pe_elem_identUpd:
 "pe_elem_upd p (\<lambda>a. a) = (\<lambda>a. a)"
  by(rule ext, simp add: pe_elem_upd,rule nth_equalityI,simp_all)
(* No identUpd rule exists for p_elem_upd *)
lemma ie_elem_identUpd:
 "ie_elem_upd snd = (\<lambda>a. a)"
  by(rule ext, simp add: ie_elem_upd,rule nth_equalityI,simp_all)
lemma i_elem_identUpd:
 "i_elem_upd (nth a) a = a"
  by(simp add: i_elem_upd,rule nth_equalityI,simp_all)
lemma e_elem_identUpd:
 "e_elem_upd (\<lambda>a. a) = (\<lambda>a. a)"
  by(rule ext, simp add: e_elem_upd)
(* No identUpd rule exists for elem_upd *)

lemma spie_elem_sameUpd:
 "spie_elem_upd sp (\<lambda>(i,_). u (i,the ((sp_elem_map sp a) i))) a = spie_elem_upd sp u a"
  by(simp add: spie_elem_upd sp_elem_map iexcerpt_def)
(* The sameUpd rule is trivial for spi_elem_upd *)
(* No sameUpd rule exists for spe_elem_upd *)
(* The sameUpd rule is trivial for sp_elem_upd *)
lemma sie_elem_sameUpd:
 "sie_elem_upd s (\<lambda>(i,_). u (i,the ((s_elem_map s a) i))) a = sie_elem_upd s u a"
  by(simp add: sie_elem_upd s_elem_map iexcerpt_def)
(* The sameUpd rule is trivial for si_elem_upd *)
(* No sameUpd rule exists for se_elem_upd *)
(* The sameUpd rule is trivial for s_elem_upd *)
lemma pie_elem_sameUpd:
 "pie_elem_upd p (\<lambda>(i,_). u (i,the ((p_elem_map p a) i))) a = pie_elem_upd p u a"
  by(simp add: pie_elem_upd p_elem_map iexcerpt_def)
(* The sameUpd rule is trivial for pi_elem_upd *)
(* No sameUpd rule exists for pe_elem_upd *)
(* The sameUpd rule is trivial for p_elem_upd *)
lemma ie_elem_sameUpd:
 "ie_elem_upd (\<lambda>(i,_). u (i,the ((elem_map a) i))) a = ie_elem_upd u a"
  by(simp add: ie_elem_upd elem_map iexcerpt_def)
(* The sameUpd rule is trivial for i_elem_upd *)
(* No sameUpd rule exists for e_elem_upd *)
(* The sameUpd rule is trivial for elem_upd *)

lemma spie_elem_prtprtUpd:
 "\<lbrakk>sp = (sp_app sp' a)\<rbrakk> \<Longrightarrow>
  sp_elem_map sp (spie_elem_upd sp' u a) = sp_upd_map sp sp' u a"
  apply(rule sp_observe_update_only_update'[where sp''=sp'])
  by(simp_all add: sp_dis_def iexcerpt_def)
lemma spi_elem_prtprtUpd:
 "\<lbrakk>sp = (sp_app sp' a)\<rbrakk> \<Longrightarrow>
  sp_elem_map sp (spi_elem_upd sp' u a) = sp_upd_map sp sp' (u\<circ>fst) a"
  by(simp add: spi_elem_upd_def spie_elem_prtprtUpd)
lemma spe_elem_prtprtUpd:
 "\<lbrakk>sp = (sp_app sp' a)\<rbrakk> \<Longrightarrow>
  sp_elem_map sp (spe_elem_upd sp' u a) = sp_upd_map sp sp' (u\<circ>snd) a"
  by(simp add: spe_elem_upd_def spie_elem_prtprtUpd)
lemma sp_elem_prtprtUpd:
 "\<lbrakk>sp = (sp_app sp' a)\<rbrakk> \<Longrightarrow>
  sp_elem_map sp (sp_elem_upd sp' v a) = sp_upd_map sp sp' (\<lambda>_.v) a"
  by(simp add: sp_elem_upd_def spie_elem_prtprtUpd)
lemma sie_elem_prtprtUpd:
 "s_elem_map s (sie_elem_upd s u a) = s_upd_map s s u a"
  apply(simp add: s_elem_map_def sie_elem_upd_def s_upd_map_def)
  apply(rule spie_elem_prtprtUpd)
  by(auto simp add: sp_app_def)
lemma si_elem_prtprtUpd:
 "s_elem_map s (si_elem_upd s u a) = s_upd_map s s (u\<circ>fst) a"
  by(simp add: si_elem_upd_def sie_elem_upd_def[symmetric] sie_elem_prtprtUpd)
lemma se_elem_prtprtUpd:
 "s_elem_map s (se_elem_upd s u a) = s_upd_map s s (u\<circ>snd) a"
  by(simp add: se_elem_upd_def sie_elem_upd_def[symmetric] sie_elem_prtprtUpd)
lemma s_elem_prtprtUpd:
 "s_elem_map s (s_elem_upd s v a) = s_upd_map s s (\<lambda>_.v) a"
  apply(simp add: s_elem_upd_def sie_elem_upd_def[symmetric] sie_elem_prtprtUpd)
  by(auto simp add: comp_def)
(* No prtprtUpd rules exist for pie/pi/pe/p_elem_upd *)
lemma ie_elem_prtprtUpd:
 "elem_map (ie_elem_upd u a) = upd_map u a"
  apply(simp add: elem_map_def ie_elem_upd_def upd_map_def)
  apply(rule spie_elem_prtprtUpd)
  by(auto simp add: sp_app_def)
lemma i_elem_prtprtUpd:
 "elem_map (i_elem_upd u a) = upd_map (u\<circ>fst) a"
  by(simp add: i_elem_upd_def ie_elem_upd_def[symmetric] ie_elem_prtprtUpd)
lemma e_elem_prtprtUpd:
 "elem_map (e_elem_upd u a) = upd_map (u\<circ>snd) a"
  by(simp add: e_elem_upd_def ie_elem_upd_def[symmetric] ie_elem_prtprtUpd)
lemma elem_prtprtUpd:
 "elem_map (elem_upd v a) = upd_map (\<lambda>_.v) a"
  apply(simp add: elem_upd_def ie_elem_upd_def[symmetric] ie_elem_prtprtUpd)
  by(auto simp add: comp_def)

lemma spie_elem_commUpd:
 "\<lbrakk>sp_dis sp1 sp2 a\<rbrakk> \<Longrightarrow> 
  (spie_elem_upd (sp_app sp1 a) u1 \<circ> spie_elem_upd sp2 u2) a = (spie_elem_upd (sp_app sp2 a) u2 \<circ> spie_elem_upd sp1 u1) a"
  by(auto simp add: spie_elem_upd comp_snd_def sp_dis_def iexcerpt_def sp_app_def)
lemma spi_elem_commUpd:
 "\<lbrakk>sp_dis sp1 sp2 a\<rbrakk> \<Longrightarrow> 
  (spi_elem_upd (sp_app sp1 a) u1 \<circ> spi_elem_upd sp2 u2) a = (spi_elem_upd (sp_app sp2 a) u2 \<circ> spi_elem_upd sp1 u1) a"
  by(auto simp add: spi_elem_upd comp_snd_def sp_dis_def iexcerpt_def sp_app_def)
lemma spe_elem_commUpd:
 "\<lbrakk>sp_dis sp1 sp2 a\<rbrakk> \<Longrightarrow> 
  (spe_elem_upd (sp_app sp1 a) u1 \<circ> spe_elem_upd sp2 u2) a = (spe_elem_upd (sp_app sp2 a) u2 \<circ> spe_elem_upd sp1 u1) a"
  by(auto simp add: spe_elem_upd comp_snd_def sp_dis_def iexcerpt_def sp_app_def)
lemma sp_elem_commUpd:
 "\<lbrakk>sp_dis sp1 sp2 a\<rbrakk> \<Longrightarrow> 
  (sp_elem_upd (sp_app sp1 a) v1 \<circ> sp_elem_upd sp2 v2) a = (sp_elem_upd (sp_app sp2 a) v2 \<circ> sp_elem_upd sp1 v1) a"
  by(auto simp add: sp_elem_upd comp_snd_def sp_dis_def iexcerpt_def sp_app_def)
lemma sie_elem_commUpd:
 "\<lbrakk>s1 \<sqinter> s2 = \<bottom>\<rbrakk> \<Longrightarrow> 
  (sie_elem_upd s1 u1 \<circ> sie_elem_upd s2 u2) = (sie_elem_upd s2 u2 \<circ> sie_elem_upd s1 u1)"
  apply(auto simp add: sie_elem_upd comp_snd_def iexcerpt_def)
  by(rule ext,auto,drule_tac x=xa in disjoint_pred,auto)
lemma si_elem_commUpd:
 "\<lbrakk>s1 \<sqinter> s2 = \<bottom>\<rbrakk> \<Longrightarrow> 
  (si_elem_upd s1 u1 \<circ> si_elem_upd s2 u2) = (si_elem_upd s2 u2 \<circ> si_elem_upd s1 u1)"
  apply(auto simp add: si_elem_upd comp_snd_def iexcerpt_def)
  by(rule ext,auto,drule_tac x=xa in disjoint_pred,auto)
lemma se_elem_commUpd:
 "\<lbrakk>s1 \<sqinter> s2 = \<bottom>\<rbrakk> \<Longrightarrow> 
  (se_elem_upd s1 u1 \<circ> se_elem_upd s2 u2) = (se_elem_upd s2 u2 \<circ> se_elem_upd s1 u1)"
  apply(auto simp add: se_elem_upd comp_snd_def iexcerpt_def)
  by(rule ext,auto,drule_tac x=xa in disjoint_pred,auto)
lemma s_elem_commUpd:
 "\<lbrakk>s1 \<sqinter> s2 = \<bottom>\<rbrakk> \<Longrightarrow> 
  (s_elem_upd s1 v1 \<circ> s_elem_upd s2 v2) = (s_elem_upd s2 v2 \<circ> s_elem_upd s1 v1)"
  apply(auto simp add: s_elem_upd comp_snd_def iexcerpt_def)
  by(rule ext,auto,drule_tac x=xa in disjoint_pred,auto)
(* No commUpd rules exist for pie/pi/pe/p_elem_upd *)
(* No commUpd rules exist for ie_/i_/e_/elem_upd *)

lemmas spie_elem_absrbUpd = sp_observe_update_no_update'

end
