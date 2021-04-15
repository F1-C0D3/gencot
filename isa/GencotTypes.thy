theory GencotTypes
  imports "HOL-Library.Type_Length"
begin

text \<open>The type of lists with a fixed length, used for representing C arrays\<close>

typedef (overloaded) ('n::len, 'a) FixedList =  "{x::'a list. length x = LENGTH('n)}"
  apply (rule_tac x = "replicate LENGTH('n) (_::'a)" in exI)
  by simp

lemma length_FixedList: "length (Rep_FixedList x) = LENGTH('n)" for x::"('n::len, 'a) FixedList"
  apply(insert Rep_FixedList)
  by auto

end