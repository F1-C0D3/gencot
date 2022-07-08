theory Gencot_SemanticsSupport
  imports 
    Gencot_PartAccessSupport
    Gencot_ArraySupport
    "HOL-Word.Word"
begin
ML \<open>structure sem = Named_Thms (val name = Binding.name "sem" val description = "")\<close>
setup \<open> sem.setup \<close>
ML \<open>structure sem_defs = Named_Thms (val name = Binding.name "sem_defs" val description = "")\<close>
setup \<open> sem_defs.setup \<close>

text \<open>Automatically eliminate \<open>ucast\<close> with the simplifier.\<close>
lemma aux_power_mono: "\<lbrakk>(n::nat) < 2^x; x \<le> y\<rbrakk> \<Longrightarrow> n < 2^y"
  using not_less_iff_gr_or_eq order.strict_trans by fastforce

lemma ucast_eliminate[simp]: 
 "LENGTH('a) \<le> LENGTH('b) \<Longrightarrow> unat ((ucast (n:: 'a::len word)):: 'b::len word) = unat n"
  apply(unat_arith)
  apply(simp add: ucast_def unat_def uint_word_of_int)
  apply(drule_tac y="LENGTH('b)" and n=naa in aux_power_mono) 
   by(auto) 

end
