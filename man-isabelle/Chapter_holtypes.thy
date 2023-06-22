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
The type of boolean values is specified equivalent to an algebraic type of the form
of the enmeration type (see Section~\ref{holbasic-data-constr})
@{theory_text[display]
\<open>datatype bool = True | False\<close>}

The type \<open>bool\<close> plays a special role in HOL since it is the type of all terms which are used 
as propositions and facts (see Section~\ref{basic-theory-prop}.
\<close>

subsection "Values"
text_raw\<open>\label{holtypes-bool-values}\<close>

text\<open>
Values of type \<open>bool\<close> can directly be denoted by the parameterless constructors \<open>True\<close> and \<open>False\<close>.
\<close>

subsection "Destructors and Conditional Terms"
text_raw\<open>\label{holtypes-bool-destrs}\<close>

text\<open>
Since both constructors are constant no selectors can be defined. Discriminators are not required
since the constants are already boolean values.

A \<open>case\<close> term for type \<open>bool\<close> has the form
@{text[display]
\<open>case term of True \<Rightarrow> term\<^sub>1 | False \<Rightarrow> term\<^sub>2\<close>}
where \<open>term\<close> is a term of type \<open>bool\<close>.

As an alternative syntax Isabelle provides the usual form
@{text[display]
\<open>if term then term\<^sub>1 else term\<^sub>2\<close>}
\<close>

subsection "Functions"
text_raw\<open>\label{holtypes-bool-funcs}\<close>

text\<open>
The usual logical functions are defined for type \<open>bool\<close>: \<open>conj, disj, implies, iff\<close>
of type \<open>bool \<Rightarrow> bool \<Rightarrow> bool\<close> with infix forms \<open>\<and>, \<or>, \<longrightarrow>, \<longleftrightarrow>\<close> and the unary negation \<open>Not\<close>
of type \<open>bool \<Rightarrow> bool\<close> and alternate form \<open>\<not>\<close>.
\<close>

text \<open>
\<^item> \<open>\<forall>, \<exists>\<close>
\<^item> intro
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
The type of natural numbers is specified equivalent to a recursive algebraic type (see 
Section~\ref{holbasic-data}) of the form
@{theory_text[display]
\<open>datatype nat = 0 | Suc nat\<close>}
It is not really defined in this way, because \<open>0\<close> is not a constructor, but it can mainly be used
in the same way.

The type \<open>nat\<close> denotes the mathematical concept of natural numbers, it has infinitely many values,
there is no upper limit.
\<close>

subsection "Values"
text_raw\<open>\label{holtypes-nat-values}\<close>

text\<open>
Values of type \<open>nat\<close> can be denoted in the usual way using constructor expressions such as \<open>Suc 0,
Suc (Suc 0), \<dots>\<close>.

Alternatively they can be denoted by decimal number literals such as \<open>0, 1, 2, \<dots>\<close> of arbitrary size.

However, the decimal number literals are overloaded and may also denote values of other numerical
types, such as type \<open>int\<close> for the integer numbers. Therefore the type of an isolated decimal number
literal is not determined, which may cause unexpected effects. To denote a value of type \<open>nat\<close> its
type may be explicitly specified as described in Section~\ref{basic-theory-terms}, such as \<open>1::nat\<close>.
\<close>

subsection "Destructors"
text_raw\<open>\label{holtypes-nat-destrs}\<close>

text\<open>
Since \<open>Suc\<close> plays the role of a constructor, corresponding destructors can be defined.
The selector function which inverts \<open>Suc\<close> is defined as \<open>nat.pred\<close> where \<open>nat.pred x\<close> is equivalent
to \<open>x - 1\<close> and \<open>nat.pred 0 = 0\<close>. There are no discriminators, instead the equality term \<open>x = 0\<close> and
\<open>x \<noteq> 0\<close> can be used.

A \<open>case\<close> term for type \<open>nat\<close> has the form
@{text[display]
\<open>case term of 0 \<Rightarrow> term\<^sub>1 | Suc n \<Rightarrow> term\<^sub>2\<close>}
where \<open>term\<close> is a term of type \<open>nat\<close>.
\<close>

subsection "Functions"
text_raw\<open>\label{holtypes-nat-funcs}\<close>

text\<open>
The usual basic arithmetic functions are defined for type \<open>nat\<close>: \<open>plus, minus, times, divide, modulo\<close>
of type \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close> with infix forms \<open>+, -, *, div, mod\<close> and alternate form \<open>/\<close> for \<open>div\<close>.
Subtraction is truncated at \<open>0\<close>, e.g. \<open>4 - 7\<close> evaluates to \<open>0\<close>. Also defined are the binary functions
\<open>min, max\<close>.

As predicates of type \<open>nat \<Rightarrow> nat \<Rightarrow> bool\<close> are defined \<open>less, less_eq, greater, greater_eq\<close> with infix
forms \<open><, \<le>, >, \<ge>\<close> and the ``divides'' predicate \<open>dvd\<close> (infix only).

Like decimal number literals all these functions are overloaded and not restricted to natural
numbers. As a consequence, a proposition such as 
@{theory_text[display]
\<open>4 - 7 = 0\<close>}
is not valid and cannot be proven. To become a provable fact it must be specified in a form like
@{theory_text[display]
\<open>(4::nat) - 7 = 0\<close>}
which can be proven by method \<open>simp\<close>. Note that it is sufficient to specify the type for a single
literal, because then the type of the function \<open>-\<close> is derived to be \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close> (there are
no ``mixed-typed'' arithmetic functions) from which the type of the second literal is derived and
similar for the equality.
\<close>

subsection "Rules"
text_raw\<open>\label{holtypes-nat-rules}\<close>

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