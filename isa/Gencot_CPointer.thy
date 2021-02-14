theory Gencot_CPointer
  imports ShallowShared
  "HOL-Library.Adhoc_Overloading"
begin

axiomatization where getPtr_def[simp]: "\<forall>x . getPtr x = CPtr.cont\<^sub>f x" 
axiomatization where setPtr_def[simp]: "\<forall>arg . setPtr arg = RR.make (CPtr.make (RR.p2\<^sub>f arg)) ()"
axiomatization where exchngPtr_def[simp]: 
  "\<forall> arg . exchngPtr arg = RR.make (CPtr.make (RR.p2\<^sub>f arg)) (CPtr.cont\<^sub>f (RR.p1\<^sub>f arg))"
axiomatization where modifyPtr_def[simp]: 
  "\<forall> arg . modifyPtr arg = 
     (let p=RR.p1\<^sub>f arg; chf = RR.p1\<^sub>f (RR.p2\<^sub>f arg); inp = RR.p2\<^sub>f (RR.p2\<^sub>f arg);
         chres = chf (RR.make (CPtr.cont\<^sub>f p) inp) 
     in RR.make (CPtr.make (RR.p1\<^sub>f chres)) (RR.p2\<^sub>f chres))"

end
