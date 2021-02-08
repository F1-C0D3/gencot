theory Gencot_CPointer
  imports ShallowShared
begin

axiomatization where getPtr_def[simp]: "\<forall>x . getPtr x = CPtr.cont\<^sub>f x" 

end
