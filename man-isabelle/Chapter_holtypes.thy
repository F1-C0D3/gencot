theory Chapter_holtypes
  imports Chapter_holbasic
begin

chapter "Isabelle HOL Types"
text_raw\<open>\label{holtypes}\<close>

text \<open>
This chapter introduces a small basic part of the types available in HOL. The selected types are
considered useful for some forms of program verification.

Most of the types are algebraic types (see Section~\ref{holbasic-data}). Although some of them are
defined differently for technical reasons, they are configured afterwards to behave as if they 
have been defined as algebraic types. Therefore they are described here using the corresponding
datatype definition.
\<close>

section "Boolean Values"
text_raw\<open>\label{holtypes-bool}\<close>

text\<open>
**todo**
\<close>

text \<open>
\<^item> \<open>\<and>, \<or>, \<not>, \<longrightarrow>\<close>
\<^item> \<open>=, \<noteq>, \<longleftrightarrow>\<close>
\<^item> \<open>\<forall>, \<exists>\<close>
\<^item> intro
\<close>

subsection "Conditional Terms"
text_raw\<open>\label{holtypes-bool-if}\<close>

text\<open>
**todo**
\<close>

subsection "Logic Rules"
text_raw\<open>\label{holtypes-bool-rules}\<close>

text\<open>
**todo**
\<close>

text \<open>
\<^item> conjI, conjE, disjI1, disjI2, disjE, impI, mp
\<^item> contrapos\_*
\<^item> iffI, iffE, iffD1, iffD2
\<^item> allI, allE, exI, exE
\<close>


section "Natural Numbers"
text_raw\<open>\label{holtypes-nat}\<close>

text\<open>
**todo**
\<close>

section "Tuple Types"
text_raw\<open>\label{holtypes-tup}\<close>

text \<open>
Tuple types are constructed by cartesian product of existing types. Tuple types can be directly denoted 
by type expressions of the form
@{text[display]
\<open>t\<^sub>1 \<times> \<dots> \<times> t\<^sub>n\<close>}
in inner syntax. It is not necessary to introduce a name to use a tuple type, however, this is possible
by defining a type synonym (see Section~\ref{basic-theory-types}):
@{theory_text[display]
\<open>type_synonym t = t\<^sub>1 \<times> \<dots> \<times> t\<^sub>n\<close>}
\<close>

subsection "Tuple Values"

text\<open>
**todo**
\<close>

section "Optional Values"
text_raw\<open>\label{holtypes-option}\<close>

text\<open>
**todo**
\<close>

section "Sets"
text_raw\<open>\label{holtypes-set}\<close>

text\<open>
**todo**
\<close>

section "Lists"
text_raw\<open>\label{holtypes-list}\<close>

text\<open>
**todo**
\<close>

section "Fixed-Size Binary Numbers"
text_raw\<open>\label{holtypes-word}\<close>

text\<open>
**todo**
\<close>

end