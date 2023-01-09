theory Chapter_hol
  imports Chapter_basic
begin

chapter "Isabelle HOL"
text_raw\<open>\label{hol}\<close>

section "Type Definitions"
text_raw\<open>\label{hol-typedefs}\<close>

text \<open>
\<^item> typedef
\<^item> datatype
\<^item> record
\<close>

section "Terms"
text_raw\<open>\label{hol-terms}\<close>

text \<open>
\<^item> let
\<^item> case
\<^item> if
\<close>

section "Types"
text_raw\<open>\label{hol-types}\<close>

subsection "Boolean Values"
text_raw\<open>\label{hol-types-bool}\<close>

text \<open>
\<^item> \<open>\<and>, \<or>, \<not>, \<longrightarrow>\<close>
\<^item> \<open>=, \<noteq>, \<longleftrightarrow>\<close>
\<^item> \<open>\<forall>, \<exists>\<close>
\<^item> intro
\<close>

subsection "Sets"
text_raw\<open>\label{hol-types-set}\<close>

subsection "Natural Numbers"
text_raw\<open>\label{hol-types-nat}\<close>

subsection "Tuples"
text_raw\<open>\label{hol-types-tuple}\<close>

subsection "Lists"
text_raw\<open>\label{hol-types-list}\<close>

subsection "Fixed-Size Binary Numbers"
text_raw\<open>\label{hol-types-word}\<close>

(*

section "Logic Rules"
text_raw\<open>\label{hol-logrul}\<close>

text \<open>
\<^item> conjI, conjE, disjI1, disjI2, disjE, impI, mp
\<^item> contrapos\_*
\<^item> iffI, iffE, iffD1, iffD2
\<^item> allI, allE, exI, exE
\<close>

section "Lifting and Transfer"
text_raw\<open>\label{hol-lift}\<close>

*)
end