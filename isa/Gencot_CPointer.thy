theory Gencot_CPointer
  imports ShallowShared
  "HOL-Library.Adhoc_Overloading"
begin

axiomatization where getPtr_def[simp]: "\<forall>x . getPtr x = CPtr.cont\<^sub>f x" 
axiomatization where setPtr_def[simp]: "\<forall>arg . setPtr arg = makeTup2 (CPtr.make (p2Tup2 arg)) ()"
axiomatization where exchngPtr_def[simp]: 
  "\<forall> arg . exchngPtr arg = makeTup2 (CPtr.make (p2Tup2 arg)) (CPtr.cont\<^sub>f (p1Tup2 arg))"
axiomatization where modifyPtr_def[simp]: 
  "\<forall> arg . modifyPtr arg = 
     (let p=p1Tup2 arg; chf = p1Tup2 (p2Tup2 arg); inp = p2Tup2 (p2Tup2 arg);
         chres = chf (makeTup2 (CPtr.cont\<^sub>f p) inp) 
     in makeTup2 (CPtr.make (p1Tup2 chres)) (p2Tup2 chres))"

end
