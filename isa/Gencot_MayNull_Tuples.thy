theory Gencot_MayNull_Tuples
  imports ShallowShared_Tuples
begin

axiomatization where null_def[simp]: "null () = option.None" 
axiomatization where mayNull_def[simp]: "\<forall>x . mayNull x = option.Some x" 
axiomatization where notNull_def[simp]: "\<forall>x . notNull x = (case x of option.None \<Rightarrow> None () | option.Some y \<Rightarrow> Some y)" 
axiomatization where roNotNull_def[simp]: "\<forall>x . roNotNull x = (case x of option.None \<Rightarrow> None () | option.Some y \<Rightarrow> Some y)" 

end