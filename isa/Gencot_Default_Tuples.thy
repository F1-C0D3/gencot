theory Gencot_Default_Tuples
  imports ShallowShared_Tuples
begin

overloading
  defaultVal_unit \<equiv> "defaultVal :: unit \<Rightarrow> unit"
  defaultVal_word \<equiv> "defaultVal :: unit \<Rightarrow> ('a::len0) word"
begin
  definition defaultVal_unit :: "unit \<Rightarrow> unit"
    where "defaultVal_unit x \<equiv> x"
  definition defaultVal_word :: "unit \<Rightarrow> ('a::len0) word"
    where "defaultVal_word x \<equiv> 0"
end
end