section \<open>Array Support\<close>

text \<open>
These theories provide support for representing arrays from programming languages as lists. An array with
elements of a type \<open>'el\<close> is represented by lists of type \<open>'el list\<close>. The theories define
observation and modification functions for modeling the use of arrays in programs and develop abstract
views on it. The main characteristics of the defined functions is that list elements are associated with an index
counted from \<open>0\<close> and that modification functions never modify the list length.
\<close>

theory Gencot_ArraySupport
  imports Gencot_ArrayPrefixSupport
begin

end
