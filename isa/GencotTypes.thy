theory GencotTypes
  imports "HOL-Library.Numeral_Type"
begin

text \<open>The type of lists with a fixed length, used for representing C arrays\<close>

typedef ('n::finite, 'a) FixedList =  "{x::'a list. length x = CARD('n)}"
apply (rule_tac x = "replicate CARD('n) (_::'a)" in exI)
  by simp

text \<open>
  Type MayNull is represented using HOL.option. 
  Since Cogent common also defines a type Option with the same variants,
  we make the HOL.option variant names available by alias names.\<close>
abbreviation HOLSome where "HOLSome \<equiv> Some"
abbreviation HOLNone where "HOLNone \<equiv> None"

end