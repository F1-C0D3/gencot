section \<open>Array Support\<close>

theory Gencot_ArraySingleSupport
  imports Gencot_ArrayModifSupport
begin

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

lemma elm_sp_elem_map:
 "iexcerpt sp a i \<Longrightarrow> elm i a = the (sp_elem_map sp a i)"
  by(simp add: elm_def elem_map_def sp_elem_map iexcerpt_def)

lemma elm_take:
 "\<lbrakk>vld a i; i < j\<rbrakk> \<Longrightarrow> elm i (take j a) = elm i a"
  apply(subst elm_def,simp add: elem_map_def sp_elem_map_take)
  by(subst elm_sp_elem_map[symmetric],simp_all add: iexcerpt_def iprefx)

lemma elm_zip:
 "\<lbrakk>vld a1 i; vld a2 i\<rbrakk> \<Longrightarrow>
  elm i (zip a1 a2) = (elm i a1, elm i a2)"
  by(simp add: elm)

lemma elm_map:
 "vld a i \<Longrightarrow> elm i (map f a) = f (elm i a)"
  by(simp add: elm)

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

subsubsection \<open>Access Single Elements after Update\<close>

lemma elm_spie_elem_upd:
 "\<lbrakk>vld a i; sp (i, elm i a)\<rbrakk> \<Longrightarrow> elm i (spie_elem_upd sp u a) = u (i, elm i a)"
  by(simp add: elm spie_elem_upd iexcerpt_def)
lemma elm_spi_elem_upd:
 "\<lbrakk>vld a i; sp (i, elm i a)\<rbrakk> \<Longrightarrow> elm i (spi_elem_upd sp u a) = u i"
  by(simp add: elm spi_elem_upd iexcerpt_def)
lemma elm_spe_elem_upd:
 "\<lbrakk>vld a i; sp (i, elm i a)\<rbrakk> \<Longrightarrow> elm i (spe_elem_upd sp u a) = u (elm i a)"
  by(simp add: elm spe_elem_upd iexcerpt_def)
lemma elm_sp_elem_upd:
 "\<lbrakk>vld a i; sp (i, elm i a)\<rbrakk> \<Longrightarrow> elm i (sp_elem_upd sp v a) = v"
  by(simp add: elm sp_elem_upd iexcerpt_def)
lemma elm_sie_elem_upd:
 "\<lbrakk>vld a i; s i\<rbrakk> \<Longrightarrow> elm i (sie_elem_upd s u a) = u (i, elm i a)"
  by(simp add: elm sie_elem_upd)
lemma elm_si_elem_upd:
 "\<lbrakk>vld a i; s i\<rbrakk> \<Longrightarrow> elm i (si_elem_upd s u a) = u i"
  by(simp add: elm si_elem_upd)
lemma elm_se_elem_upd:
 "\<lbrakk>vld a i; s i\<rbrakk> \<Longrightarrow> elm i (se_elem_upd s u a) = u (elm i a)"
  by(simp add: elm se_elem_upd)
lemma elm_s_elem_upd:
 "\<lbrakk>vld a i; s i\<rbrakk> \<Longrightarrow> elm i (s_elem_upd s v a) = v"
  by(simp add: elm s_elem_upd)
lemma elm_pie_elem_upd:
 "\<lbrakk>vld a i; p (elm i a)\<rbrakk> \<Longrightarrow> elm i (pie_elem_upd p u a) = u (i, elm i a)"
  by(simp add: elm pie_elem_upd)
lemma elm_pi_elem_upd:
 "\<lbrakk>vld a i; p (elm i a)\<rbrakk> \<Longrightarrow> elm i (pi_elem_upd p u a) = u i"
  by(simp add: elm pi_elem_upd)
lemma elm_pe_elem_upd:
 "\<lbrakk>vld a i; p (elm i a)\<rbrakk> \<Longrightarrow> elm i (pe_elem_upd p u a) = u (elm i a)"
  by(simp add: elm pe_elem_upd)
lemma elm_p_elem_upd:
 "\<lbrakk>vld a i; p (elm i a)\<rbrakk> \<Longrightarrow> elm i (p_elem_upd p v a) = v"
  by(simp add: elm p_elem_upd)
lemma elm_ie_elem_upd:
 "\<lbrakk>vld a i\<rbrakk> \<Longrightarrow> elm i (ie_elem_upd u a) = u (i, elm i a)"
  by(simp add: elm ie_elem_upd)
lemma elm_i_elem_upd:
 "\<lbrakk>vld a i\<rbrakk> \<Longrightarrow> elm i (i_elem_upd u a) = u i"
  by(simp add: elm i_elem_upd)
lemma elm_e_elem_upd:
 "\<lbrakk>vld a i\<rbrakk> \<Longrightarrow> elm i (e_elem_upd u a) = u (elm i a)"
  by(simp add: elm e_elem_upd)
lemma elm_elem_upd:
 "\<lbrakk>vld a i\<rbrakk> \<Longrightarrow> elm i (elem_upd v a) = v"
  by(simp add: elm elem_upd)

end
