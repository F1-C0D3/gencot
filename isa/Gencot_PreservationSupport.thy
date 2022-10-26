section \<open>Preservation Support\<close>

theory Gencot_PreservationSupport
  imports Main
begin

text \<open>
This theory introduces the predicate \<open>prsv\<close> which states that a modification function on
a data structure preserves an observation on the data structure.
\<close>

definition prsv :: "('x \<Rightarrow> 'y) \<Rightarrow> ('x \<Rightarrow> 'x) \<Rightarrow> bool"
  where "prsv f u \<equiv> f = f \<circ> u"

text \<open>
The following rule is added to the simpset. It allows the simplifier to substitute \<open>f (u x)\<close> by  
\<open>f x\<close> if it can prove \<open>prsv f u\<close>.
\<close>
lemma prsv[simp]: "prsv f u \<Longrightarrow> f (u x) = f x"
  by(simp add: prsv_def comp_def,metis)

text \<open>
The predicate \<open>prsvp\<close> preserves a boolean observation but is weaker than \<open>prsv\<close> for a 
boolean observation (a predicate) because it only states the implication from the old value to the 
modified value. In other words, the negated predicate is not preserved. This is useful
for a modification function which does not depend on the old value and simply sets a new
value. It may preserve the predicate, by simply setting only elements which satisfy the predicate, 
but it cannot also preserve the negated predicate.
\<close>

definition prsvp :: "('x \<Rightarrow> bool) \<Rightarrow> ('x \<Rightarrow> 'x) \<Rightarrow> bool"
  where "prsvp p f \<equiv> \<forall>x. p x \<longrightarrow> p (f x)"


end

