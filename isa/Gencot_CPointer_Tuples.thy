theory Gencot_CPointer_Tuples
  imports ShallowShared_Tuples
begin

axiomatization where getPtr_def[simp]: "\<forall>x . getPtr x = CPtr.cont\<^sub>f x" 
axiomatization where setPtr_def[simp]: "\<forall>arg . setPtr arg = (CPtr.make (snd arg), ())"
axiomatization where exchngPtr_def[simp]: 
  "\<forall> arg . exchngPtr arg = (CPtr.make (snd arg), CPtr.cont\<^sub>f (fst arg))"
axiomatization where modifyPtr_def[simp]: 
  "\<forall> arg . modifyPtr arg = 
     (let p = fst arg; chf = fst (snd arg); inp = snd (snd arg);
         chres = chf (CPtr.cont\<^sub>f p, inp) 
     in (CPtr.make (fst chres), snd chres))"

end
