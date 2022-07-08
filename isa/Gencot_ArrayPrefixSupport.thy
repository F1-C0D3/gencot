section \<open>Array Support\<close>

theory Gencot_ArrayPrefixSupport
  imports Gencot_ArraySingleSupport
begin

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
lemma isingl_indx_fst_map:
 "vld a i \<Longrightarrow> sr_indx_fst_map (isingl i,r) a = (\<lambda>x. if r x (nth a i) then Some i else None)"
  apply(simp add: sr_indx_fst_map_def isingl sp_indx_fst rexcrp_def iexcerpt_def)
  apply(rule ext,auto simp add: iexcerpt_def)
  by(rule Least_equality,simp_all)

lemma isingl_indx_fst_map':
 "(sr_indx_fst_map (isingl i,r) a x = Some i) = (vld a i \<and> r x (elm i a))"
  apply(simp add: sr_indx_fst_map_def isingl sp_indx_fst rexcrp_def iexcerpt_def)
  apply(auto simp add: elm)
  by(rule Least_equality,simp_all)

text \<open>
Induction start: the empty prefix cannot contain a matching element.
\<close>
lemma iprefx_indx_fst_map_start:
 "sr_indx_fst_map (iprefx 0,r) a x = None"
  by(simp add: sr_indx_fst_map_def iprefx rexcrp_def sp_indx_fst iexcerpt_def)

text \<open>
Induction step: the result of the successor prefix is the result of the prefix, if found there,
otherwise the result of the successor match.
\<close>
lemma iprefx_indx_fst_map_step:
 "sr_indx_fst_map (iprefx (Suc i), r) a x =
  (if sr_indx_fst_map (iprefx i,r) a x = None 
  then sr_indx_fst_map (isingl i,r) a x
  else sr_indx_fst_map (iprefx i,r) a x)"
  apply(subst isingl_iprefx[symmetric])
  apply(auto simp add: sr_indx_fst_map_S_union)
  apply(case_tac "sr_indx_fst_map (isingl i, r) a x",simp_all)
  apply(drule sr_indx_fst_map_satisfies_sr)+
  by(auto simp add: iprefx isingl)

text \<open>
A prefix up to the array length covers the whole array.
\<close>
lemma iprefx_indx_fst_map_all:
 "i = length a \<Longrightarrow>
  sr_indx_fst_map (iprefx i, r) a = 
  r_indx_fst_map r a"
  apply(unfold sr_indx_fst_map_def r_indx_fst_map_def)
  apply(rule ext)
  apply(subst sp_to_p_indx_fst[where p="r x"])
  apply(simp_all add: rexcrp_def iprefx)
  apply(rule sp_to_p_indx_fst[symmetric])
  by(simp)

text \<open>
Unique search:
\<close>

text \<open>
If the elements in the successor prefix are distinct and the element at the last index is found
by a parameter \<open>x\<close>, no element can be found by \<open>x\<close> in the prefix.
\<close>
lemma iprefx_indx_fst_map_uniq:
 "\<lbrakk>sr_uniq (iprefx (Suc i), r) a; vld a i; r x (elm i a)\<rbrakk> \<Longrightarrow> 
  sr_indx_fst_map (iprefx i,r) a x = None"
  apply(rule_tac ?s1.0="isingl i" and i=i in sr_uniq_union)
  by(simp_all add: isingl_iprefx isingl_iprefx_bot isingl_indx_fst_map')

text \<open>
If the elements in the prefix are distinct but not in the successor prefix, then the element at 
the last index can be found by a parameter \<open>x\<close>, which also finds an element in the prefix.
\<close>
lemma iprefx_indx_fst_map_non_uniq:
 "\<lbrakk>\<not> sr_uniq (iprefx (Suc i), r) a; sr_uniq (iprefx i,r) a\<rbrakk> \<Longrightarrow> 
  \<exists> x j. r x (elm i a) \<and> sr_indx_fst_map (iprefx i,r) a x = Some j"
  apply(simp add: isingl_iprefx[symmetric])
  apply(drule sr_non_uniq_union,simp_all add: isingl_iprefx_bot sr_uniq_isingl)
  apply(auto)
  apply(frule sr_indx_fst_map_satisfies_sr,simp add: isingl, erule conjE)
  apply(frule sr_indx_fst_map_valid)
  by(rule_tac x=x in exI,simp add:elm)

text \<open>
Specific case of injectivity for the last index, then if there is a parameter \<open>x\<close> related
to the element at the last index, it finds an element in the prefix.
\<close>
lemma iprefx_indx_fst_map_non_uniq_injective:
 "\<lbrakk>\<not> sr_uniq (iprefx (Suc i), r) a; sr_uniq (iprefx i,r) a; 
  sr_injective (isingl i,r) a; vld a i; r x (elm i a)\<rbrakk> \<Longrightarrow> 
  \<exists> j. sr_indx_fst_map (iprefx i,r) a x = Some j"
  apply(drule iprefx_indx_fst_map_non_uniq,simp,clarsimp)
  apply(rule_tac x=j in exI)
  apply(subgoal_tac "x = xa",simp)
  apply(drule inj_sr_indx_fst_map)
  apply(rule_tac m="sr_indx_fst_map (isingl i, r) a" and y=i in inj_map)
  by(simp_all add: isingl_indx_fst_map')

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
  apply(rule ext,simp)
  by(rule spie_elem_upd_id, auto simp add: pprefx iexcerpt_def)
lemma spi_elem_upd_start:
 "spi_elem_upd (pprefx (0,p)) u = id"
  apply(rule ext,simp)
  by(rule spi_elem_upd_id, auto simp add: pprefx iexcerpt_def)
lemma spe_elem_upd_start:
 "spe_elem_upd (pprefx (0,p)) u = id"
  apply(rule ext,simp)
  by(rule spe_elem_upd_id, auto simp add: pprefx iexcerpt_def)
lemma sp_elem_upd_start:
 "sp_elem_upd (pprefx (0,p)) v = id"
  apply(rule ext,simp)
  by(rule sp_elem_upd_id, auto simp add: pprefx iexcerpt_def)
lemma sie_elem_upd_start:
 "sie_elem_upd (iprefx 0) u = id"
  apply(rule ext,simp)
  by(rule sie_elem_upd_id, auto simp add: iprefx)
lemma si_elem_upd_start:
 "si_elem_upd (iprefx 0) u = id"
  apply(rule ext,simp)
  by(rule si_elem_upd_id, auto simp add: iprefx)
lemma se_elem_upd_start:
 "se_elem_upd (iprefx 0) u = id"
  apply(rule ext,simp)
  by(rule se_elem_upd_id, auto simp add: iprefx)
lemma s_elem_upd_start:
 "s_elem_upd (iprefx 0) v = id"
  apply(rule ext,simp)
  by(rule s_elem_upd_id, auto simp add: iprefx)

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
