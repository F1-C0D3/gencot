theory Gencot_SemanticsSupport
  imports 
    Gencot_PartAccessSupport
    Gencot_ArraySupport
begin
ML \<open>structure sem = Named_Thms (val name = Binding.name "sem" val description = "")\<close>
setup \<open> sem.setup \<close>
ML \<open>structure sem_defs = Named_Thms (val name = Binding.name "sem_defs" val description = "")\<close>
setup \<open> sem_defs.setup \<close>
end
