theory Chapter_basic
  imports Chapter_system
begin
chapter "Isabelle Basics"
text_raw\<open>\label{basic}\<close>

text \<open>
The basic mechanisms of Isabelle mainly support defining types, constants, and functions and 
specifying and proving statements about them.
\<close>

section "Isabelle Theories"
text_raw\<open>\label{basic-theory}\<close>

text \<open>
A theory is the content of an Isabelle theory file.
\<close>

subsection "Theory Structure"
text_raw\<open>\label{basic-theory-structure}\<close>

text \<open>
The content of a theory file has the structure
@{theory_text[display]
\<open>theory name
imports name\<^sub>1 \<dots> name\<^sub>n
begin
  \<dots>
end\<close>}
where \<^theory_text>\<open>name\<close> is the theory name and \<^theory_text>\<open>name\<^sub>1 \<dots> name\<^sub>n\<close> are the names of the imported theories.
The theory name \<^theory_text>\<open>name\<close> must be the same which is used for the theory file, i.e., the file name 
must be \<^verbatim>\<open>name.thy\<close>.

The theory structure is a part of the Isabelle ``outer syntax'' which is mainly fixed and independent
from the specific theories. Other kind of syntax is embedded into the outer syntax. The main embedded
syntax is the ``inner syntax'' which is mainly used to denote types and terms. Content in inner
syntax must always be surrounded by double quotes. The only exception is a single isolated identifier,
for it the quotes may be omitted.

This introduction describes only a selected part of the outer syntax. The full outer syntax is described
in the Isabelle/Isar Reference Manual.

Additionally, text written in \LaTeX\ syntax can be embedded into the outer syntax using the form
\<^theory_text>\<open>text\<open> \<dots> \<close>\<close>
and \LaTeX\ sections can be created using
\<^theory_text>\<open>chapter\<open> \<dots> \<close>\<close>, \<^theory_text>\<open>section\<open> \<dots> \<close>\<close>, \<^theory_text>\<open>subsection\<open> \<dots> \<close>\<close>, \<^theory_text>\<open>subsubsection\<open> \<dots> \<close>\<close>, \<^theory_text>\<open>paragraph\<open> \<dots> \<close>\<close>,
\<^theory_text>\<open>subparagraph\<open> \<dots> \<close>\<close>.
Note that the delimiters used here are not the ``lower'' and ``greater'' symbols, but the ``cartouche
delimiters'' available in the editor's Symbols panel in tab ``Punctuation''.

Embedded \LaTeX\ text is intended for additional explanations of the formal theory content. It is
displayed in the session document together with the formal theory content.

It is also possible to embed inner and outer syntax in the \LaTeX\ syntax (see Chapter 4 in the 
Isabelle/Isar Reference Manual).

Moreover, comments of the form
\begin{verbatim}
  (* ... *)
\end{verbatim}
can be embedded into the outer syntax. They are only intended for the reader of the theory file
and are not displayed in the session document.
\<close>

subsection "Types"
text_raw\<open>\label{basic-theory-types}\<close>

text \<open>
As usual in formal logics, the basic building blocks of propositions are terms. Terms denote arbitrary
objects like numbers, sets, functions, or boolean values. Isabelle is strongly typed, so every term 
must have a type. However, in most situations Isabelle can derive the type of a term automatically,
so that it needs not be specified explicitly. Terms and types are always denoted using the inner syntax.

Types are usually specified by type names. In Isabelle HOL (see Chapter~\ref{holbasic}) there are 
predefined types such as \<open>nat\<close> and \<open>bool\<close>
for natural numbers and boolean values. New types can be defined in the form
@{theory_text[display]
\<open>typedecl name\<close>}
which introduces the \<^theory_text>\<open>name\<close> for a new type for which the values are different from the values of 
all existing types and the set of values is not empty. No other information about the values is 
given, that must be done separately. See Chapter~\ref{holbasic} for ways of defining types with
specifying more information about their values.

Types can be parameterized, then the type arguments are denoted \<^emph>\<open>before\<close> the type name, such as in
\<open>nat set\<close> which is the type of sets of natural numbers. A type name with \<open>n\<close> parameters is declared
in the form
@{theory_text[display]
\<open>typedecl ('name\<^sub>1,\<dots>,'name\<^sub>n) name\<close>}
such as \<^theory_text>\<open>typedecl ('a) set\<close>. The type parameters are denoted by ``type variables'' which always have the 
form \<open>'name\<close> with a leading single quote
character. Every use where the parameters are replaced by actual types, such 
as in \<open>nat set\<close>, is called an ``instance'' of the parameterized type.

Alternatively a type name can be introduced as a synonym for an existing type in the form
@{theory_text[display]
\<open>type_synonym name = type\<close>}
such as in \<^theory_text>\<open>type_synonym natset = nat set\<close>. Type synonyms can also be parameterized as in
@{theory_text[display]
\<open>type_synonym ('name\<^sub>1,\<dots>,'name\<^sub>n) name = type\<close>}
where the type variables occur in \<open>type\<close> in place of actual type specifications.
\<close>

subsection "Terms"
text_raw\<open>\label{basic-theory-terms}\<close>

subsubsection "Constants and Variables"

text \<open>
Terms are mainly built as syntactical structures based on constants and variables. Constants are usually
denoted by names, using the same namespace as type names. Whether a name denotes a constant or a 
type depends on its position in a term. Predefined constant names of type \<open>bool\<close> are \<open>True\<close> and 
\<open>False\<close>.

Constants of number types, such as \<open>nat\<close>, may be denoted by number literals, such as \<open>6\<close>
or \<open>42\<close>.

A constant can be defined by specifying its type. The definition
@{theory_text[display]
\<open>consts name\<^sub>1 :: type\<^sub>1 \<dots> name\<^sub>n :: type\<^sub>n\<close>}
introduces \<open>n\<close> constants with their names and types. No information is specified about the 
constant's values, in this respect the constants are ``underspecified''. The information about the
values must be specified separately.

If the constant's type contains type variables the constant is called ``polymorphic''. Thus the 
declaration
@{theory_text[display]
\<open>consts myset :: "'a set"\<close>}
declares the polymorphic constant \<open>myset\<close> which may be a set of elements of arbitrary type.

A (term) variable has the same form as a constant name, but it has not been introduced as a 
constant. Whenever a variable is used in a term it has a specific type which is either derived 
from its context or is explicitly specified in the form \<open>varname :: type\<close>.

Nested terms are generally written by using parentheses \<open>(\<dots>)\<close>. There are many priority rules how 
to nest terms automatically, but if in doubt, it is always safe to use parentheses.
\<close>
 
subsubsection "Functions"

text \<open>
A constant name denotes an object, which, according to its type, may also be a function of 
arbitrary order. Functions basically have a single argument. The type of a function is written 
as \<open>argtype \<Rightarrow> restype\<close>. 

Functions in Isabelle are always total, i.e., they map every value of type \<open>argtype\<close> to some value
of type \<open>restype\<close>. However, a function may be ``underspecified'' so that no information is (yet)
available about the result value for some or all argument values. A function defined by
@{theory_text[display]
\<open>consts mystery :: nat \<Rightarrow> nat\<close>}
is completely underspecified: although it maps every natural number to a unique other natural number
no information about these numbers is available. Functions may also be partially specified by 
describing the result value only for some argument values. This does not mean that the function is
``partial'' and has no value for the remaining arguments. The information about these values may
always be provided later, this does not ``modify'' the function, it only adds information about it.
\<close>

subsubsection "Functions with Multiple Arguments"

text\<open>
The result type
of a function may again be a function type, then it may be applied to another argument. This is used
to represent functions with more than one argument. Function types are right associative, thus a 
type \<open>argtype\<^sub>1 \<Rightarrow> argtype\<^sub>2 \<Rightarrow> \<cdots> \<Rightarrow> argtype\<^sub>n \<Rightarrow> restype\<close> describes a function which can be applied 
to \<open>n\<close> arguments. 

Function application terms for a function \<open>f\<close> and an argument \<open>a\<close> are denoted by
\<open>f a\<close>, no parentheses are required around the argument. Function application terms are left 
associative, thus a function application to \<open>n\<close> arguments is written \<open>f a\<^sub>1 \<dots> a\<^sub>n\<close>. Note that an
application \<open>f a\<^sub>1 \<dots> a\<^sub>m\<close> where \<open>m < n\<close> (a ``partial application'') is a correct term and denotes a
function taking the remaining \<open>n-m\<close> arguments.

For every constant alternative syntax forms may be defined for application terms. This is often used
for binary functions to represent application terms in infix notation with an operator symbol.
As an example, the name for the addition function is \<open>plus\<close>, so an application term is denoted
in the form \<open>plus 3 5\<close>. For \<open>plus\<close> an alternative syntax is defined as infix notation using the
operator symbol \<open>+\<close>, therefore the application term can also be denoted by \<open>3 + 5\<close>. Similar infix
notations are supported for many basic functions, using operator symbols such as \<open>-\<close>, \<open>**\<close>, \<open>=\<close>, 
\<open>\<noteq>\<close>, \<open>\<le>\<close>, or \<open>\<in>\<close>. 
\<close>

subsubsection "Lambda-Terms"

text\<open>
Functions can be denoted by lambda terms of the form \<open>\<lambda>x. term\<close> where \<open>x\<close> is a variable
which may occur in the \<open>term\<close>. A function to be applied to \<open>n\<close> arguments can be denoted by the
lambda term \<open>\<lambda>x\<^sub>1 \<dots> x\<^sub>n. term\<close> where \<open>x\<^sub>1 \<dots> x\<^sub>n\<close> are distinct variables. As usual, types may be
specified for (some of) the variables in the form \<open>\<lambda>(x\<^sub>1::t\<^sub>1) \<dots> (x\<^sub>n::t\<^sub>n). term\<close>.
\<close>

subsection "Definitions and Abbreviations"
text_raw\<open>\label{basic-theory-definition}\<close>

text \<open>
A constant name may be introduced together with information about its associated value by specifying 
a term for the value. There are two forms for introducing constant names in this way, definitions and abbreviations.
\<close>

subsubsection "Definitions"

text\<open>
A definition defines a new constant together with its type and value.
It is denoted in the form
@{theory_text[display]
\<open>definition name :: type
where "name \<equiv> term"\<close>}
Note that the ``defining equation'' \<open>name \<equiv> term\<close> is specified in inner syntax and, like \<open>type\<close> 
must be delimited by quotes. The \<open>name\<close> may not occur in the \<open>term\<close>, i.e., this form of definition
do not support recursion.

If the type of the defined name is a function type, the \<open>term\<close> may be a lambda term. Alternatively,
the definition for a function applicable to \<open>n\<close> arguments can be written in the form
@{theory_text[display]
\<open>definition name :: type
where "name x\<^sub>1 \<dots> x\<^sub>n \<equiv> term"\<close>}
with variable names \<open>x\<^sub>1 \<dots> x\<^sub>n\<close> which may occur in the \<open>term\<close>. This form is mainly equivalent to
@{theory_text[display]
\<open>definition name :: type
where "name \<equiv> \<lambda>x\<^sub>1 \<dots> x\<^sub>n. term"\<close>}

A short form of a definition is
@{theory_text[display]
\<open>definition "name \<equiv> term"\<close>}
Here, the type of the new constant is derived as the type of the \<open>term\<close>.

Usually, a constant defined in this way is fully specified, i.e., all information about its value
is available. However, if the term does not provide this information, the constant is still 
underspecified. Consider the definition
@{theory_text[display]
\<open>definition "mystery2 \<equiv> mystery"\<close>}
where \<open>mystery\<close> is defined as above. Then it is only known that \<open>mystery2\<close> has type \<open>nat \<Rightarrow> nat\<close> and
is the same total function as \<open>mystery\<close>, but nothing is known about its values.
\<close>

subsubsection "Abbreviations"

text\<open>
An abbreviation definition does not define a constant, it only introduces the name 
as a synonym for a term. Upon input the name is automatically expanded, and upon output it is used 
whenever a term matches its specification and the term is not too complex. 
An abbreviation definition is denoted in a similar form as a definition:
@{theory_text[display]
\<open>abbreviation name :: type
where "name \<equiv> term"\<close>}
As for definitions, recursion is not supported, the \<open>name\<close> may not occur in the \<open>term\<close>. The short
form is also available as for definitions.

The alternative form for functions is also available. The abbreviation definition
@{theory_text[display]
\<open>abbreviation name :: type
where "name x\<^sub>1 \<dots> x\<^sub>n \<equiv> term"\<close>}
introduces a ``parameterized'' abbreviation. An application term \<open>name term\<^sub>1 \<dots> term\<^sub>n\<close> is replaced
upon input by \<open>term\<close> where all occurrences of \<open>x\<^sub>i\<close> have been substituted by \<open>term\<^sub>i\<close>. Upon output
terms are matched with the structure of \<open>term\<close> and if successful a corresponding application term
is constructed and displayed.
\<close>

subsection "Overloading"
text_raw\<open>\label{basic-theory-overload}\<close>

subsubsection "True Overloading"

text \<open>
One way of providing information about the value of an underspecified constant is overloading.
It provides the information with the help of another constant together with a definition for it.

Overloading depends on the type. Therefore, if a constant is 
polymorphic, different definitions can be associated for different type instances.

Overloading is only possible for constants which do not yet have a definition, i.e., they must
have been defined by \<^theory_text>\<open>consts\<close> (see Section~\ref{basic-theory-terms}).
Such a constant \<open>name\<close> is associated with \<open>n\<close> definitions by the following overloading
specification:
@{theory_text[display]
\<open>overloading
  name\<^sub>1 \<equiv> name
    \<dots>
  name\<^sub>n \<equiv> name
begin
  definition name\<^sub>1 :: type\<^sub>1 where \<dots>
    \<dots>
  definition name\<^sub>n :: type\<^sub>n where \<dots>
end\<close>}
where all \<open>type\<^sub>i\<close> must be instances of the type declared for \<open>name\<close>.

The auxiliary constants \<open>name\<^sub>1 \<dots> name\<^sub>n\<close> are only introduced locally and cannot be used outside
of the \<^theory_text>\<open>overloading\<close> specification.
\<close>

subsubsection "Adhoc Overloading"

text\<open>
There is also a form of overloading which achieves similar effects although it is implemented
completely differently. It is only performed on the syntactic level, like abbreviations.
To use it, the theory \<^theory>\<open>HOL-Library.Adhoc_Overloading\<close> must be imported by the surrounding
theory:
@{theory_text[display]
\<open>imports "HOL-Library.Adhoc_Overloading"\<close>}
(Here the theory name must be quoted because it contains a minus sign.)

Then a constant name \<open>name\<close> can be defined to be a ``type dependent abbreviation''
for \<open>n\<close> terms of different type instances by
@{theory_text[display]
\<open>adhoc_overloading name term\<^sub>1 \<dots> term\<^sub>n\<close>}
Upon input the type of \<open>name\<close> is determined from the context, then it is replaced by the 
corresponding \<open>term\<^sub>i\<close>. Upon output terms are matched with the corresponding \<open>term\<^sub>i\<close> and if 
successful \<open>name\<close> is displayed instead.

Although \<open>name\<close> must be the name of an existing constant, only its type is used. The constant is
not affected by the adhoc overloading, however, it becomes inaccessible because its name is now
used as term abbreviation. 

Several constant names can be overloaded in a common specification:
@{theory_text[display]
\<open>adhoc_overloading name\<^sub>1 term\<^sub>1\<^sub>1 \<dots> term\<^sub>1\<^sub>n and \<dots> and name\<^sub>k \<dots>\<close>}
\<close>

subsection "Propositions"
text_raw\<open>\label{basic-theory-prop}\<close>

text \<open>
A proposition denotes a statement, which can be valid or not. Valid statements are called
``facts'', they are the main content of a theory. Propositions are specific terms and
are hence written in inner syntax and must be enclosed in quotes.
\<close>
subsubsection "Formulas"

text \<open>
In its simplest form a proposition is a single term of type \<open>bool\<close>, such as
@{text[display]
\<open>6 * 7 = 42\<close>}
Terms of type \<open>bool\<close> are also called ``formulas''.

A proposition may contain free variables as in
@{text[display]
\<open>2 * x = x + x\<close>}

A formula as proposition is valid if it evaluates to \<open>True\<close> for all possible values substituted
for the free variables.
\<close>

subsubsection "Derivation Rules"

text \<open>
More complex propositions can express, ``derivation rules'' used to derive propositions
from other propositions. Derivation rules are denoted using a ``metalogic language''. It is
still written in inner syntax but uses a small set of ``metalogic operators''. 

Derivation rules consist of assumptions and a conclusion. They can be written using the metalogic
operator \<open>\<Longrightarrow>\<close> in the form
@{text[display]
\<open>A\<^sub>1 \<Longrightarrow> \<cdots> \<Longrightarrow> A\<^sub>n \<Longrightarrow> C\<close>}
where the \<open>A\<^sub>1 \<dots> A\<^sub>n\<close> are the assumptions and \<open>C\<close> is the conclusion. The conclusion must be a formula. 
The assumptions may be arbitrary propositions. If an assumption contains metalogic operators 
parentheses can be used to delimit them from the rest of the derivation rule.

A derivation rule states that if the assumptions are valid, the conclusion can be derived
as also being valid. So it can be viewed as a ``meta implication'' with a similar meaning as a 
boolean implication, but with a different use.

An example for a rule with a single assumption is
@{text[display]
\<open>(x::nat) < c \<Longrightarrow> n*x \<le> n*c\<close>}
Note that type \<open>nat\<close> is explicitly specified for variable \<open>x\<close>. This is necessary, because the
constants \<open><\<close>, \<open>*\<close>, and \<open>\<le>\<close> are overloaded and can be applied to other types than only natural
numbers. Therefore the type of \<open>x\<close> cannot be derived automatically. However, when the type of
\<open>x\<close> is known, the types of \<open>c\<close> and \<open>n\<close> can be derived to also be \<open>nat\<close>.

An example for a rule with two assumptions is
@{text[display]
\<open>(x::nat) < c \<Longrightarrow> n > 0 \<Longrightarrow> n*x < n*c\<close>}

In most cases the assumptions are also formulae, as in the example. However, they may also
be again derivation rules. Then the rule is a ``meta rule'' which derives a proposition from other 
rules. This introductory manual usually does not take such meta rules into account.
\<close>

subsubsection "Binding Free Variables"

text \<open>
A proposition may contain universally bound variables, using the metalogic quantifier \<open>\<And>\<close> in the
form
@{text[display]
\<open>\<And> x\<^sub>1 \<dots> x\<^sub>n. P\<close>}
where the \<open>x\<^sub>1 \<dots> x\<^sub>n\<close> may occur free in the proposition \<open>P\<close>. As usual, types may be
specified for (some of) the variables in the form \<open>\<And> (x\<^sub>1::t\<^sub>1) \<dots> (x\<^sub>n::t\<^sub>n). P\<close>. An example for
a valid derivation rule with bound variables is
@{text[display]
\<open>\<And> (x::nat) c n . x < c \<Longrightarrow> n*x \<le> n*c\<close>}

If a standalone proposition contains free variables they are implicitly universally bound. Thus
the example derivation rule above is equivalent to the single-assumption example rule in the 
previous section. Explicit binding of variables is only required to avoid name clashes with 
constants of the same name. In the proposition
@{text[display]
\<open>\<And> (True::nat). True < c \<Longrightarrow> n*True \<le> n*c\<close>}
the name \<open>True\<close> is used locally as a variable of type \<open>nat\<close> instead of the predefined constant
of type \<open>bool\<close>. Of course, using well known constant names as variables is confusing and should
be avoided.
\<close>

subsubsection "Alternative Rule Syntax"

text \<open>
An alternative, Isabelle specific syntax for derivation rules is
@{text[display]
\<open>\<And> x\<^sub>1 \<dots> x\<^sub>m. \<lbrakk>A\<^sub>1; \<dots>; A\<^sub>n\<rbrakk> \<Longrightarrow> C\<close>}
which is often considered as more readable, because it better separates the assumptions from the
conclusion. In the interactive editor it may be necessary to switch to this form by setting 
\<^verbatim>\<open>Print Mode\<close> to \<^verbatim>\<open>brackets\<close> in \<^verbatim>\<open>Plugin Options\<close> for \<^verbatim>\<open>Isabelle General\<close>. The fat brackets are
available for input in the editor's Symbols panel in tab ``Punctuation''.

Using this syntax the two-assumption example rule from the previous section is denoted by
@{text[display]
\<open>\<And> (x::nat) c n. \<lbrakk>x < c; n > 0\<rbrakk> \<Longrightarrow> n*x < n*c\<close>}
or equivalently without quantifier by
@{text[display]
\<open>\<lbrakk>(x::nat) < c; n > 0\<rbrakk> \<Longrightarrow> n*x < n*c\<close>}

Note that in the literature a derivation rule @{thm conjI[no_vars]} is often denoted in the form
@{thm[display,mode=Rule] conjI[no_vars]}

Another alternative, Isabelle specific syntax for a derivation rule 
\<open>\<And> x\<^sub>1 \<dots> x\<^sub>m. \<lbrakk>A\<^sub>1; \<dots>; A\<^sub>n\<rbrakk> \<Longrightarrow> C\<close> is the ``structured'' proposition 
@{theory_text[display]
\<open>"C" if "A\<^sub>1" \<dots> "A\<^sub>n" for x\<^sub>1 \<dots> x\<^sub>m\<close>}
The assumptions and the variables
may be grouped or separated for better readability by the keyword \<^theory_text>\<open>and\<close>. For every group of 
variables a type may be specified in the usual form, it applies to all variables in the group. 
Note that the keywords \<^theory_text>\<open>if\<close>, \<^theory_text>\<open>and\<close>, \<^theory_text>\<open>for\<close> belong to the outer syntax. Thus, the original rule
must be quoted as a whole, whereas in the structured proposition only the sub-propositions
\<open>C, A\<^sub>1, \<dots>, A\<^sub>n\<close> must be individually quoted. The \<open>x\<^sub>1, \<dots>, x\<^sub>m\<close> need not be quoted, but if a
type is specified for a variable the type must be quoted, if it is not a single type name.

If written in this form, the two-assumption example rule from the previous subsections becomes
@{theory_text[display]
\<open>"n*x < n*c" if "x < c" and "n > 0" for x::nat and n c\<close>}
\<close>

subsection "Theorems"
text_raw\<open>\label{basic-theory-theorem}\<close>

text \<open>
A theorem specifies a proposition together with a proof, that the proposition is valid. Thus it
adds a fact to the enclosing theory. A simple form of a theorem is
@{theory_text[display]
\<open>theorem "prop" \<proof>\<close>}
where \<open>prop\<close> is a proposition in inner syntax and \<^theory_text>\<open>\<proof>\<close> is a proof as described in 
Section \ref{basic-proof}. The keyword \<^theory_text>\<open>theorem\<close> can be replaced by one of the keywords
\<^theory_text>\<open>lemma\<close>, \<^theory_text>\<open>corollary\<close>, \<^theory_text>\<open>proposition\<close> to give a hint about the use of the statement to
the reader.
\<close>

subsubsection "Unknowns"

text \<open>
Whenever a theorem turns a proposition to a fact, the free (or universally bound) variables
are replaced by ``unknowns''. For a variable \<open>name\<close> the corresponding unknown is \<open>?name\<close>.
This is only a technical difference, it signals to Isabelle that the unknowns can be 
consistently substituted by arbitrary terms, as long as the types are preserved.

When turned to a fact, the example rule from the previous sections becomes
@{text[display]
\<open>?x < ?c \<Longrightarrow> ?n*?x \<le> ?n*?c\<close>}
with type \<open>nat\<close> associated to all unknowns.

The result of such a substitution is always a special case of the fact and therefore also
a fact. In this way a fact with unknowns gives rise to a (usually infinite) number of facts
which are constructed by substituting unknowns by terms.

Isabelle can be configured to suppress the question mark when displaying unknowns, then
this technical difference becomes invisible.
\<close>

subsubsection "Named Facts"

text \<open>
Facts are often used in proofs of other facts. For this purpose they can be named so 
that they can be referenced by name. A named fact is specified by a theorem of the form
@{theory_text[display]
\<open>theorem name: "prop" \<proof>\<close>}

The example rule from the previous sections can be turned into a fact named \<open>example1\<close> by
@{theory_text[display]
\<open>theorem example1: "(x::nat) < c \<Longrightarrow> n*x \<le> n*c" \<proof>\<close>}

It is also possible to introduce named collections of facts. A simple way to introduce
such a named collection is 
@{theory_text[display]
\<open>lemmas name = name\<^sub>1 \<dots> name\<^sub>n\<close>}
where \<open>name\<^sub>1 \<dots> name\<^sub>n\<close> are names of existing facts or fact collections.

If there is a second rule stated as a named fact by
@{theory_text[display]
\<open>theorem example2: "(x::nat) \<le> c \<Longrightarrow> x + m \<le> c + m" \<proof>\<close>}
a named collection can be introduced by
@{theory_text[display]
\<open>lemmas examples = example1 example2\<close>}

Alternatively a ``dynamic fact set'' can be declared by
@{theory_text[display]
\<open>named_theorems name\<close>}
It can be used as a ``bucket'' where facts can be added afterwards by specifying the bucket
name in the theorem:
@{theory_text[display]
\<open>theorem [name]: "prop" \<proof>\<close>}
or together with specifying a fixed fact name \<^theory_text>\<open>name\<^sub>f\<close> by
@{theory_text[display]
\<open>theorem name\<^sub>f[name]: "prop" \<proof>\<close>}

A named fact or fact set (but not a dynamic fact set) can be displayed using the
command
@{theory_text[display]
\<open>thm name\<close>}
which may be entered outside of theorems and at most positions in a proof. The facts
are displayed in the Output panel (see Section~\ref{system-jedit-output}).
\<close>

subsubsection "Alternative Theorem Syntax"

text \<open>
There is an alternative syntax for theorems which have a derivation rule as their proposition.
A theorem \<^theory_text>\<open>theorem "\<And> x\<^sub>1 \<dots> x\<^sub>m. \<lbrakk>A\<^sub>1; \<dots>; A\<^sub>n\<rbrakk> \<Longrightarrow> C" \<proof>\<close> can also be specified in the form
@{theory_text[display]
\<open>theorem 
  fixes x\<^sub>1 \<dots> x\<^sub>m
  assumes "A\<^sub>1" \<dots> "A\<^sub>n"
  shows "C"
  \<proof>\<close>}
Similar to the structured proposition form, the variables and assumptions may be grouped by 
\<^theory_text>\<open>and\<close>, the keywords belong to the outer syntax and the \<open>C, A\<^sub>1, \<dots>, A\<^sub>n\<close> must be individually quoted.

Using this syntax the two-assumption example rule from the previous sections can be written as
@{theory_text[display]
\<open>theorem 
  fixes x::nat and c n
  assumes "x < c" and "n > 0"
  shows "n*x < n*c"
  \<proof>\<close>}

In contrast to the general theorem syntax this alternative syntax allows to specify names 
for some or all of the assumption groups as
@{theory_text[display]
\<open>assumes name\<^sub>1: "A\<^sub>1\<^sub>1" \<dots> "A\<^sub>1\<^sub>m\<^sub>1" and \<dots> and name\<^sub>n: "A\<^sub>n\<^sub>1" \<dots> "A\<^sub>n\<^sub>m\<^sub>n"\<close>}
These names can (only) be used in the proof of the theorem. More consequences this syntax has
for the proof are described in Section~\ref{basic-proof}.

Note that a name specified for the conclusion as
@{theory_text[display]
\<open>shows name: "C"\<close>}
becomes the name for the whole fact introduced by the theorem, not only for the conclusion. It
is not available in the proof of the theorem. Alternatively the name for the fact can be specified
after the \<^theory_text>\<open>theorem\<close> keyword:
@{theory_text[display]
\<open>theorem name:
  fixes x::nat and c and n 
  assumes "x < c" and "n > 0"
  shows "n*x < n*c"
  \<proof>\<close>}
\<close>

subsubsection "Definitions as Facts"

text \<open>
The definitions described in Section~\ref{basic-theory-definition} also introduce facts in
the enclosing theory. Every definition introduces a new constant and specifies a defining
equation of the form \<open>name \<equiv> term\<close> for it. This equation is a proposition using the ``meta
equality'' \<open>\<equiv>\<close> which is another metalogic operator. It is the initial information given for
the new constant, thus it is valid ``by definition'' and is a fact in the theory.

These facts are automatically named. If \<open>name\<close> is the name of the defined constant, the 
defining equation is named \<open>name_def\<close>. Alternatively an explicit name can be specified in 
the form
@{theory_text[display]
\<open>definition name :: type
where fact_name: "name \<equiv> term"\<close>}

Although the auxiliary constants used in an \<^theory_text>\<open>overloading\<close> specification (see 
Section~\ref{basic-theory-overload}) are not accessible outside the specification, their 
definitions are. So they can be referred by their names and used as information about the 
overloaded constant.
\<close>

subsection "Locales"
text_raw\<open>\label{basic-theory-locale}\<close>

text \<open>
There are cases where theory content such as definitions and theorems occur which has similar 
structure but differs in some types or terms. Then it is useful to define a ``template'' and 
instantiate it several times. This can be done in Isabelle using a ``locale''.
\<close>

subsubsection "Simple Locales"

text \<open>
A locale can be seen as a parameterized theory fragment, where the parameters are terms. A locale
with \<open>n\<close> parameters is defined by
@{theory_text[display]
\<open>locale name = 
  fixes x\<^sub>1 \<dots> x\<^sub>n
begin
  \<dots>
end\<close>}
where the variables \<open>x\<^sub>1, \<dots>, x\<^sub>n\<close> are the parameters. Like the bound variables in a theorem they can
be grouped by \<^theory_text>\<open>and\<close> and types can be specified for some or all groups. The content between
\<^theory_text>\<open>begin\<close> and \<^theory_text>\<open>end\<close> may consist of definitions and theorems which may use the parameter names 
like constant names. Content may also be added to an existing locale in the form 
@{theory_text[display]
\<open>context name
begin
  \<dots>
end\<close>}
Therefore the \<^theory_text>\<open>begin \<dots> end\<close> block can also be omitted in the locale definition and the locale can be
filled later.

An instance of the parameterized theory fragment is created by ``interpreting'' the locale in the form
@{theory_text[display]
\<open>interpretation name term\<^sub>1 \<dots> term\<^sub>n .\<close>}
where \<open>term\<^sub>1 \<dots> term\<^sub>n\<close> are the terms to be substituted for the locale parameters, their types must
match the parameter types, i.e., must be instances of them. The final dot in the interpretation
is a rudimentary proof. An actual proof is needed, if the locale definition specifies additional
assumptions for the parameters.
\<close>

subsubsection "Locales with Assumptions"

text \<open>
Additional assumptions for locale parameters can be specified as propositions in the form
@{theory_text[display]
\<open>locale name = 
  fixes x\<^sub>1 \<dots> x\<^sub>n
  assumes A\<^sub>1 \<dots> A\<^sub>m
begin
  \<dots>
end\<close>}
where the \<open>A\<^sub>1, \<dots>, A\<^sub>m\<close> are propositions. Like in a theorem, they can be grouped by \<^theory_text>\<open>and\<close> and 
named. The names can be used to reference the assumptions as facts in proofs in the locale content. 
When the locale is interpreted, all the assumptions must be proved with the actual terms substituted 
for the parameters. Therefore the more general form of an interpretation is
@{theory_text[display]
\<open>interpretation name term\<^sub>1 \<dots> term\<^sub>n \<proof>\<close>}
\<close>

subsubsection "Extending Locales"

text \<open>
A locale may extend one or more other locales using the form
@{theory_text[display]
\<open>locale name = name\<^sub>1 + \<cdots> + name\<^sub>n +
  fixes \<dots>
  assumes \<dots>
begin
  \<dots>
end\<close>}
where \<^theory_text>\<open>name\<^sub>1 \<dots> name\<^sub>n\<close> are the names of the extended locales. Their parameters become parameters
of the defined locale, inserted before the parameters declared by the \<^theory_text>\<open>fixes \<dots>\<close> clause.
\<close>

section "Isabelle Proofs"
text_raw\<open>\label{basic-proof}\<close>

text \<open>
Every proposition stated as a fact in an Isabelle theory must be proven
immediately by specifying a proof for it. A proof may have a complex structure of several steps 
and nested sub-proofs, its structure is part of the outer syntax.
\<close>

subsection "Proof Context"
text_raw\<open>\label{basic-proof-context}\<close>

text \<open>
Every proof is performed in a temporary environment which collects facts and other proof elements.
This environment is called the ``proof context''. At the end of the proof the proof context is
disposed with all its content, only the proven fact remains in the enclosing entity.

The proof context may contain
 \<^item> Facts: as usual, facts are valid propositions. However, they need not be globally valid, 
  they can be assumed to be only valid locally during the proof. 
 \<^item> Goals: a goal is a proposition which has not yet been proven. Typically it is the duty of
  a proof to prove one or more goals in its proof context.
 \<^item> Fixed variables: fixed variables are used to denote the ``arbitrary but fixed'' objects 
  often used in a proof. They can be used in all facts and goals in the same proof context.
 \<^item> Term abbreviations: these are names introduced locally for terms. Using such names for terms
  occurring in propositions it is often possible to denote propositions in a more concise form.

The initial proof context in a theorem of the form @{theory_text\<open>theorem "prop" \<proof>\<close>} 
has the proposition \<open>prop\<close> as the only goal and is otherwise empty.
\<close>

subsection "Proof Procedure"
text_raw\<open>\label{basic-proof-proc}\<close>

text \<open>
Assume you want to prove a derivation rule \<open>A \<Longrightarrow> C\<close> with a single assumption \<open>A\<close> and the 
conclusion \<open>C\<close>. The basic procedure to build a proof for it is to construct a sequence of the form
\<open>F\<^sub>1 \<Longrightarrow> F\<^sub>2, F\<^sub>2 \<Longrightarrow> F\<^sub>3, F\<^sub>3 \<Longrightarrow> \<cdots> \<Longrightarrow> F\<^sub>n\<^sub>-\<^sub>1, F\<^sub>n\<^sub>-\<^sub>1 \<Longrightarrow> F\<^sub>n\<close> from rules \<open>RA\<^sub>i \<Longrightarrow> RC\<^sub>i\<close> for \<open>i=1\<dots>n-1\<close> 
which are already known to be valid (i.e., facts) where \<open>F\<^sub>1\<close> matches with \<open>A\<close> and \<open>RA\<^sub>1\<close>, 
\<open>F\<^sub>n\<close> matches with \<open>C\<close> and \<open>RC\<^sub>n\<^sub>-\<^sub>1\<close>, and every other \<open>F\<^sub>i\<close> matches with \<open>RA\<^sub>i\<close> and \<open>RC\<^sub>i\<^sub>-\<^sub>1\<close>.

The sequence can be constructed from left to right (called ``forward reasoning'') or from right 
to left (called ``backward reasoning'') or by a combination of both. 

Consider the rule \<open>(x::nat) < 5 \<Longrightarrow> 2*x+3 \<le> 2*5+3\<close>. A proof can be constructed from the two 
example rules \<open>example1\<close> and \<open>example2\<close> from the previous sections as the sequence
\<open>(x::nat) < 5 \<Longrightarrow> 2*x \<le> 2*5, 2*x \<le> 2*5 \<Longrightarrow> 2*x+3 \<le> 2*5+3\<close> consisting of three facts.

Forward reasoning starts by assuming \<open>A\<close> to be a local fact and incrementally constructs the
sequence from it. An intermediate result is a part \<open>F\<^sub>1 \<Longrightarrow> \<cdots> \<Longrightarrow> F\<^sub>i\<close> of
the sequence, here \<open>F\<^sub>i\<close> is the ``current fact''. A forward reasoning step consists of
stating a proposition \<open>F\<^sub>i\<^sub>+\<^sub>1\<close> and proving it to be a new local fact from the current fact \<open>F\<^sub>i\<close> 
using a valid rule \<open>RA\<^sub>i \<Longrightarrow> RC\<^sub>i\<close>. The step results in the extended sequence
\<open>F\<^sub>1 \<Longrightarrow> \<cdots> \<Longrightarrow> F\<^sub>i, F\<^sub>i \<Longrightarrow> F\<^sub>i\<^sub>+\<^sub>1\<close> and the new current fact \<open>F\<^sub>i\<^sub>+\<^sub>1\<close>. When a step successfully 
proves a current fact \<open>F\<^sub>n\<close> which matches the conclusion \<open>C\<close> the proof is complete.

Backward reasoning starts at the conclusion \<open>C\<close> of the single goal \<open>A \<Longrightarrow> C\<close> and incrementally 
constructs the sequence from it backwards. An intermediate result is a part \<open>F\<^sub>i \<Longrightarrow> \<cdots> \<Longrightarrow> F\<^sub>n\<close> 
of the sequence where \<open>F\<^sub>n\<close> matches \<open>C\<close>, here the remaining part of the sequence \<open>F\<^sub>1 \<Longrightarrow> F\<^sub>i\<close> is the 
``current goal''. 
A backward reasoning step consists of applying a proof method to \<open>F\<^sub>i\<close> which constructs a new 
current goal \<open>F\<^sub>1 \<Longrightarrow> F\<^sub>i\<^sub>-\<^sub>1\<close> and the extended sequence \<open>F\<^sub>i\<^sub>-\<^sub>1 \<Longrightarrow> F\<^sub>i, F\<^sub>i \<Longrightarrow> \<cdots> \<Longrightarrow> F\<^sub>n\<close>. When
a step produces the new current goal \<open>F\<^sub>1 \<Longrightarrow> F\<^sub>1\<close>, which is trivially valid, the proof is complete.

Note the slight difference in how the steps are specified: A forward step specifies the 
new current fact \<open>F\<^sub>i\<^sub>+\<^sub>1\<close> and then proves it. A backward step specifies the proof method, the
new current goal \<open>F\<^sub>1 \<Longrightarrow> F\<^sub>i\<^sub>-\<^sub>1\<close> is constructed by the method and is not an explicit part of the proof text.
For that reason a proof constructed by forward reasoning is usually easier to read and write
than a proof constructed by backward reasoning, since in the former case the sequence of the
facts \<open>F\<^sub>i\<close> is explicitly specified in the proof text, whereas in the latter case the sequence
of the facts \<open>F\<^sub>i\<close> is implicitly constructed and the proof text specifies only the methods.

However, since every forward reasoning step again requires a proof as its part (a ``subproof''), 
no proof can be written using only forward reasoning steps. The main idea of writing ``good''
proofs is to use nested forward reasoning until every subproof is simple enough to be done in a 
single backward reasoning step, i.e., the proof method directly goes from the conclusion to the 
assumption.
\<close>

subsubsection "Unification"

text \<open>
The matching at the beginning and end of the sequence and when joining the used rules is done
by ``unification''. Two propositions \<open>P\<close> and \<open>Q\<close> are unified by substituting terms 
for unknowns in \<open>P\<close> and \<open>Q\<close> so that the results become syntactically equal.

Since only the \<open>RA\<^sub>i \<Longrightarrow> RC\<^sub>i\<close> are facts containing unknowns, only they are modified by the
unification, \<open>A\<close> and \<open>C\<close> remain unchanged. 

Note that when an unknown is substituted by a term in \<open>RA\<^sub>i\<close>, the same unknown must be substituted 
by the same term in \<open>RC\<^sub>i\<close> and vice versa, to preserve the validness of the rule \<open>RA\<^sub>i \<Longrightarrow> RC\<^sub>i\<close>. In
other words, the sequence is usually constructed from specializations of the facts \<open>RA\<^sub>i \<Longrightarrow> RC\<^sub>i\<close>
where every conclusion is syntactically equal to the assumption of the next rule.

In the example the assumption \<open>?x < ?c\<close> of rule \<open>example1\<close> is unified with \<open>(x::nat) < 5\<close> by 
substituting the term \<open>5\<close> for the unknown \<open>?c\<close>, and the variable \<open>x\<close> for the unknown \<open>?x\<close>
resulting in the specialized rule \<open>(x::nat) < 5 \<Longrightarrow> n*x \<le> n*5\<close>.
The conclusion \<open>?x + ?m \<le> ?c + ?m\<close> of rule \<open>example2\<close> is unified with \<open>2*x+3 \<le> 2*5+3\<close> by 
substituting the term \<open>2*x\<close> for the unknown \<open>?x\<close>, the term \<open>2*5\<close> for the unknown \<open>?c\<close>, and the 
term \<open>3\<close> for the unknown \<open>?m\<close> resulting in the specialized rule 
\<open>2*x \<le> 2*5 \<Longrightarrow> 2*x+3 \<le> 2*5+3\<close>. Now the two specialized rules can be joined by substituting
the term \<open>2\<close> for the unknown \<open>?n\<close> in the first, resulting in the sequence which constitutes the
proof.
\<close>

subsubsection "Multiple Assumptions"

text \<open>
If the rule to be proven has more than one assumption \<open>A\<close> the sequence to be constructed becomes
a tree where the branches start at (copies of) the assumptions \<open>A\<^sub>1,\<dots>,A\<^sub>n\<close> and merge to finally 
lead to the conclusion \<open>C\<close>. Two branches which end in facts \<open>F\<^sub>1\<^sub>n\<close> and \<open>F\<^sub>2\<^sub>m\<close> are joined by
a step \<open>\<lbrakk>F\<^sub>1\<^sub>n;F\<^sub>2\<^sub>m\<rbrakk> \<Longrightarrow> F\<^sub>1\<close> to a common branch which continues from fact \<open>F\<^sub>1\<close>.

Now a forward reasoning step may use several current facts to prove a new current fact.
Therefore all proven local facts are stored in the proof context for possible later use.
Every forward reasoning step selects a subset of the stored local facts as the current
facts and uses them to prove a new local fact from them.

A backward reasoning step may now produce several new current goals, which belong to different
branches in the tree. A step always produces the goals for all branches, therefore the 
previous goal is never used again in a step and is removed from the proof context after the
step. When a current goal has the form \<open>A \<Longrightarrow> A\<close> the proof method ``\<^theory_text>\<open>assumption\<close>'' removes 
it from the proof context without producing a new goal. Thus a proof ends when no goal 
remains in the proof context.

The set of current goals is called the ``goal state'' of the proof. Since it is not visible
in the proof text, the interactive editor displays the current goal state in the separate State
panel and optionally also in the Output panel (see Sections~\ref{system-jedit-output} 
and~\ref{system-jedit-state}), according to the cursor position in the proof text.
\<close>

subsubsection "Proving from External Facts"

text \<open>
The branches in the fact tree need not always start at an assumption \<open>A\<^sub>i\<close>, they may also start
at an ``external'' fact which is not part of the local proof context. In such cases the used 
external facts are referenced by their names. In that way a proof can use facts from the 
enclosing theory and a subproof can use facts from the enclosing proof(s) and the enclosing 
toplevel theory.

In particular, if the proposition of a theorem has no assumptions, i.e., the proposition is a
formula and consists only of the conclusion \<open>C\<close>, every proof must start at one or more external facts.
\<close>

subsection "Basic Proof Structure"
text_raw\<open>\label{basic-proof-struct}\<close>

text \<open>
A proof is written in outer syntax and describes how the fact tree is constructed which
leads from the assumptions or external facts to the conclusion.
\<close>

subsubsection "Proof Modes"

text \<open>
When writing a proof the ``proof mode'' determines the mode of operation: whether forward
reasoning (mode: \<open>proof(state)\<close>) or backward reasoning (mode: \<open>proof(prove)\<close>) is used.

The mode names refer to what is done in the next steps: In mode \<open>proof(state)\<close> facts are
``stated'' which lead to the conclusion, whereas in mode \<open>proof(prove)\<close> the goals are 
``proven'', leading to assumptions and external facts.

At the beginning of a proof the mode is always \<open>proof(prove)\<close>, i.e., backward reasoning.
In the course of the proof it is possible to switch to forward reasoning mode \<open>proof(state)\<close>, 
but not back again. After switching to forward reasoning the proof must be completed in 
forward reasoning mode, only at the end a last backward reasoning step may be applied.

However, in forward reasoning for every stated fact a (sub-)proof must be specified, which
again starts in backward reasoning mode. This way it is possible to freely switch between 
both modes in the course of a proof with nested subproofs.
\<close>

subsubsection "Proof Syntax"

text \<open>
If \<open>BS\<^sub>i\<close> denote backward reasoning steps and \<open>FS\<^sub>i\<close> denote forward reasoning steps,
the general form of a proof is
@{theory_text[display]
\<open>BS\<^sub>1 \<dots> BS\<^sub>n
proof `BS\<^sub>n\<^sub>+\<^sub>1`
  FS\<^sub>1 \<dots> FS\<^sub>m
qed `BS\<^sub>n\<^sub>+\<^sub>2`\<close>}
The last step \<open>BS\<^sub>n\<^sub>+\<^sub>2\<close> can be omitted if it is not needed.

The part \<^theory_text>\<open>proof `BS\<^sub>n\<^sub>+\<^sub>1`\<close> switches from backward reasoning mode \<open>proof(prove)\<close> to forward
reasoning mode \<open>proof(state)\<close>.
 
The part \<^theory_text>\<open>proof \<dots> qed\<close> can be replaced by \<^theory_text>\<open>done\<close>, then the proof only consists of 
backward reasoning steps and has the form \<^theory_text>\<open>BS\<^sub>1 \<dots> BS\<^sub>n done\<close>. Such proofs are 
called ``proof scripts''.

If the backward reasoning steps \<open>BS\<^sub>1 \<dots> BS\<^sub>n\<close> are omitted the proof only consists of 
the forward reasoning part and has the form
@{theory_text[display]
\<open>proof `BS\<^sub>1`
  FS\<^sub>1 \<dots> FS\<^sub>m
qed `BS\<^sub>2`\<close>}
where \<open>BS\<^sub>2\<close> can also be omitted. Such proofs are called ``structured proofs''.

A structured proof can be so simple, that it has no forward reasoning steps. For this case
the syntax
@{theory_text[display]
\<open>by `BS\<^sub>1` `BS\<^sub>2`\<close>}
abbreviates the form \<^theory_text>\<open>proof `BS\<^sub>1` qed `BS\<^sub>2`\<close>. Again, \<open>BS\<^sub>2\<close> can be omitted which
leads to the form
@{theory_text[display]
\<open>by `BS\<^sub>1`\<close>}
In this form the proof consists of a single backward reasoning step which directly leads
from the conclusion \<open>C\<close> to the assumptions and used external facts.
\<close>

subsubsection "Fake Proofs"

text \<open>
A proof can also be specified as
@{theory_text[display]
\<open>sorry\<close>}
This is a ``fake proof'' which turns the proposition to a fact without actually proving it.

A fake proof can be specified at any point in backward reasoning mode, so it can be used to
abort a proof script in the form \<^theory_text>\<open>BS\<^sub>1 \<dots> BS\<^sub>n sorry\<close>.

A structured proof in forward reasoning mode cannot be aborted in this way, however, subproofs
can be specified as fake proofs. This makes it possible to interactively develop a structured
proof in a top-down way, by first stating all required facts with fake proofs and then replacing
the fake proofs by actual proofs.
\<close>

subsubsection "Nested Proof Contexts"

text \<open>
The proof contexts in a structured proof can be nested. In a nested context the content of the
enclosing contexts is available together with the local content. When a nested context is ended,
it is removed together with all its local content.

A nested proof context is created syntactically by enclosing forward reasoning steps in braces:
@{theory_text[display]
\<open>`FS\<^sub>1` \<dots> `FS\<^sub>m` { `FS\<^sub>m\<^sub>+\<^sub>1` \<dots> `FS\<^sub>n` } `FS\<^sub>n\<^sub>+\<^sub>1` \<dots> \<close>}
Note that according to the description until now the nested context is useless, because the facts
introduced by its forward reasoning steps are removed at its end and cannot contribute to 
the proof. How the content of a nested context can be ``exported'' and preserved for later use
will be explained further below.

For names, nested contexts behave like a usual block structure: A name can be redefined in a 
nested context, then the named object in the outer context becomes inaccessible (``shadowed'') 
in the inner context, but becomes accessible again when the inner context ends. 

When two nested contexts follow each other immediately, this has the effect of ``clearing''
the content of the inner contexts: the content of the first context is removed and the second
context starts being empty. This can be denoted by the keyword
@{theory_text[display]
\<open>next\<close>}
which can be thought of being equivalent to a pair \<open>} {\<close> of adjacent braces.

Moreover the syntax \<^theory_text>\<open>proof `method\<^sub>1` FS\<^sub>1 \<dots> FS\<^sub>n qed `method\<^sub>2`\<close> automatically wraps the forward
steps \<open>FS\<^sub>1 \<dots> FS\<^sub>n\<close> in a nested context. Therefore it is possible to denote a structured proof 
which only consists of a sequence of nested contexts without braces as
@{theory_text[display]
\<open>proof `method\<^sub>1`
  FS\<^sub>1\<^sub>1 \<dots> FS\<^sub>1\<^sub>m\<^sub>1 next FS\<^sub>2\<^sub>1 \<dots> FS\<^sub>2\<^sub>m\<^sub>2 next \<dots> next FS\<^sub>n\<^sub>1 \<dots> FS\<^sub>n\<^sub>m\<^sub>n
qed `method\<^sub>n\<^sub>+\<^sub>2`\<close>}
where each occurrence of \<^theory_text>\<open>next\<close> clears the content of the context. The goal state of the proof 
is maintained in the enclosing outermost context, thus it is preserved over the whole sequence 
of nested contexts. 
\<close>

subsection "Backward Reasoning Steps"
text_raw\<open>\label{basic-proof-backstep}\<close>

text \<open>
A backward reasoning step consist of applying a proof method.
\<close>

subsubsection "Proof Methods"

text \<open>
Proof methods are basically denoted by method names, such as \<^theory_text>\<open>standard\<close>, \<^theory_text>\<open>simp\<close>, or \<^theory_text>\<open>rule\<close>. A proof
method name can also be a symbol, such as \<open>-\<close>.

A method may have arguments, then it usually must be delimited by parentheses such as in \<open>(rule example1)\<close>
or \<^theory_text>\<open>(simp add: example2)\<close>, where \<open>example1\<close> and \<open>example2\<close> are fact names.

Methods can be applied to the goal state, they modify the goal state by removing and adding goals.

The effect of applying a method is determined by its implementation and must be known to the proof
writer. Isabelle supports a large number of proof methods. Methods used for the proofs described in
this manual are described in Section~\ref{basic-methods}. 
\<close>

subsubsection "Method Application"

text \<open>
A standalone method application step is denoted as
@{theory_text[display]
\<open>apply method\<close>}
where \<open>method\<close> denotes the proof method to be applied.

The backward reasoning steps which follow \<^theory_text>\<open>proof\<close> and \<^theory_text>\<open>qed\<close> in a structured proof
are simply denoted by the applied method. Hence the general form of a proof where all
backward reasoning steps are method applications is 
@{theory_text[display]
\<open>apply `method\<^sub>1` \<dots> apply `method\<^sub>n`
proof `method\<^sub>n\<^sub>+\<^sub>1`
  FS\<^sub>1 \<dots> FS\<^sub>m
qed `method\<^sub>n\<^sub>+\<^sub>2`\<close>}
where \<open>FS\<^sub>1 \<dots> FS\<^sub>m\<close> are forward reasoning steps.
\<close>

subsection "Forward Reasoning Steps"
text_raw\<open>\label{basic-proof-forwstep}\<close>

text \<open>
A forward reasoning step consist of stating and proving a fact.
\<close>

subsubsection "Stating a Fact"

text \<open>
A fact is stated in the form
@{theory_text[display]
\<open>have "prop" \<proof>\<close>}
where \<open>prop\<close> is a proposition in inner syntax and \<^theory_text>\<open>\<proof>\<close> is a (sub-) proof for it. This form
is similar to the specification of a theorem in a theory and has a similar effect in the local 
proof context.

As for a theorem the fact can be named:
@{theory_text[display]
\<open>have name: "prop" \<proof>\<close>}
Note that the alternative form of a theorem using \<^theory_text>\<open>fixes\<close>, \<^theory_text>\<open>assumes\<close>, and \<^theory_text>\<open>shows\<close> (see 
Section~\ref{basic-theory-theorem}) is not available for stating facts in a proof.

The subproof \<^theory_text>\<open>\<proof>\<close> uses a nested context, therefore all content of the enclosing proof
context is available there and can be referenced by name, as long as the name is not shadowed by
a redefinition in the subproof. Note that the name given to the fact to be proven cannot be used
to access it in the subproof, because it is only assigned after the proof has been finished.
\<close>

subsubsection "Proving a Goal"

text \<open>
A forward reasoning proof ends, if the last stated fact \<open>F\<^sub>n\<close> unifies with the conclusion \<open>C\<close>. Therefore
a special form of stating a fact exists, which, after proving the fact, replaces free variables
by unknowns (which is called ``exporting the fact'') and tries to unify it with the conclusion of a goal in the goal state. If successful, 
it removes the goal from the goal state:
@{theory_text[display]
\<open>show "prop" \<proof>\<close>}
The syntax is the same as for \<^theory_text>\<open>have\<close>. If the unification with some goal conclusion is not successful
the step is erroneous and the proof cannot be continued, in the interactive editor an error message is displayed.

The \<^theory_text>\<open>show\<close> step tries to match and remove a goal from the innermost enclosing proof context
which maintains a goal state. This is one way how a fact proven in a nested context can affect
an enclosing context and thus contribute to the proof there. Since the forward reasoning steps 
in a structured proof are wrapped in a nested context, while the goal state is maintained in the
enclosing outer context, the \<^theory_text>\<open>show\<close> step affects the goal state of the enclosing proof.

The \<^theory_text>\<open>have\<close> and \<^theory_text>\<open>show\<close> steps are called ``goal statements'', because they state the proposition
\<open>prop\<close> as a goal which is then proven by the \<^theory_text>\<open>\<proof>\<close>.

Note that the proposition \<open>prop\<close> in a \<^theory_text>\<open>show\<close> statement often is the same proposition which 
has been specified as conclusion \<open>C\<close> in the 
proposition \<open>\<lbrakk>A\<^sub>1;\<dots>;A\<^sub>n\<rbrakk> \<Longrightarrow> C\<close> which should be proven by the proof. To avoid repeating it, Isabelle 
automatically provides the abbreviation \<open>?thesis\<close> for it. So in the simplest case the last step 
of a forward proof can be written as
@{theory_text[display]
\<open>show ?thesis \<proof>\<close>}
The abbreviation \<open>?thesis\<close> is a single identifier, therefore it needs not be quoted.

If, however, the application of \<open>method\<close> in a structured proof \<^theory_text>\<open>proof method \<dots> \<close> modifies
the original goal, this modification is not reflected in \<open>?thesis\<close>. So a statement \<^theory_text>\<open>show ?thesis 
\<proof>\<close> will usually not work, because \<open>?thesis\<close> no more unifies with the conclusion of the 
modified goal. Instead, the proof writer must know the modified goal and specify its conclusion
explicitly as proposition in the \<^theory_text>\<open>show\<close> statement. If the \<open>method\<close> splits the goal into several new 
goals, several \<^theory_text>\<open>show\<close> statements may be needed to remove them.

To test whether a proposition unifies with the conclusion of a goal in the goal state, a \<^theory_text>\<open>show\<close> 
statement can be specified with a fake proof:
@{theory_text[display]
\<open>show "prop" sorry\<close>}
If that statement is accepted, the proposition unifies with the conclusion of a goal and removes it.
\<close>

subsection "Facts as Proof Input"
text_raw\<open>\label{basic-proof-this}\<close>

text \<open>
If a linear fact sequence \<open>F\<^sub>1 \<Longrightarrow> \<cdots> \<Longrightarrow> F\<^sub>n\<close> is constructed in forward reasoning mode in the form
@{theory_text[display]
\<open>have "F\<^sub>1" `\<proof>\<^sub>1`
\<dots>
have "F\<^sub>n" `\<proof>\<^sub>n`\<close>}
every fact \<open>F\<^sub>i\<close> needs to refer to the previous fact \<open>F\<^sub>i\<^sub>-\<^sub>1\<close> in its proof \<open>proof\<^sub>i\<close>. This can be 
done by naming all facts 
@{theory_text[display]
\<open>have name\<^sub>1: "F\<^sub>1" `\<proof>\<^sub>1`
\<dots>
have name\<^sub>n: "F\<^sub>n" `\<proof>\<^sub>n`\<close>}
and refer to \<open>F\<^sub>i\<^sub>-\<^sub>1\<close> in \<open>proof\<^sub>i\<close> by \<open>name\<^sub>i\<^sub>-\<^sub>1\<close>.

Isabelle supports an alternative way by passing facts as input to a proof.
\<close>

subsubsection "Using Input Facts in a Proof"

text \<open>
The input facts are passed as input to the first method applied in the proof. In a proof script
it is the method applied in the first \<^theory_text>\<open>apply\<close> step, in a structured proof \<^theory_text>\<open>proof method \<dots>\<close> it 
is \<open>method\<close>. 

Every proof method accepts a set of facts as input. Whether it processes them and how it uses
them depends on the kind of method. Therefore input facts for a proof only work in the desired 
way, if a corresponding method is used at the beginning of the proof. See Section~\ref{basic-methods}
for descriptions how methods process input facts.
\<close>

subsubsection "Inputting Facts into a Proof"

text \<open>
In backward reasoning mode \<open>proof(prove)\<close> facts can be input to the remaining proof 
\<^theory_text>\<open>\<proof>\<close> by
@{theory_text[display]
\<open>using name\<^sub>1 \<dots> name\<^sub>n \<proof>\<close>}
where the \<open>name\<^sub>i\<close> are names of facts or fact sets. The union of all referred facts is input 
to the proof following the \<^theory_text>\<open>using\<close> specification. In a proof script it is input to the next
\<^theory_text>\<open>apply\<close> step. If a structured proof follows, it is input to its initial method. Since in 
backward reasoning mode no local facts are stated by previous steps, only external facts 
can be input this way.

In forward reasoning mode \<open>proof(state)\<close> fact input is supported with the help of the special
fact set name \<open>this\<close>. The statement
@{theory_text[display]
\<open>then\<close>}
inputs the facts named \<open>this\<close> to the proof of the following fact statement. 

The statement \<^theory_text>\<open>then\<close>
must be immediately followed by a goal statement (\<^theory_text>\<open>have\<close> or \<^theory_text>\<open>show\<close>). This is enforced by
a special third proof mode \<open>proof(chain)\<close>. In it only a goal statement is allowed, \<^theory_text>\<open>then\<close> 
switches to this mode, the goal statement switches back to mode \<open>proof(state)\<close> after its proof.

Note that \<^theory_text>\<open>then\<close> is allowed in forward reasoning mode, although it does not state a fact. There
are several other such auxiliary statements allowed in mode \<open>proof(state)\<close> in addition to the
goal statements \<^theory_text>\<open>have\<close> and \<^theory_text>\<open>show\<close>.

The fact set \<open>this\<close> can be set by the statement
@{theory_text[display]
\<open>note name\<^sub>1 \<dots> name\<^sub>n\<close>}
Therefore the statement sequence 
@{theory_text[display]
\<open>note name\<^sub>1 \<dots> name\<^sub>n
then have "prop" \<proof>\<close>}
inputs the union of all facts referred by \<open>name\<^sub>1 \<dots> name\<^sub>n\<close> to the \<^theory_text>\<open>\<proof>\<close>, in the same way
as \<^theory_text>\<open>using\<close> inputs them to the remaining proof following it.

The statement sequence
@{theory_text[display]
\<open>note name\<^sub>1 \<dots> name\<^sub>n then\<close>}
can be abbreviated by the statement
@{theory_text[display]
\<open>from name\<^sub>1 \<dots> name\<^sub>n\<close>}
Like \<^theory_text>\<open>then\<close> it switches to mode \<open>proof(chain)\<close> and it inputs the union of the facts referred by 
\<open>name\<^sub>1 \<dots> name\<^sub>n\<close> to the proof of the following goal statement.
\<close>

subsection "Fact Chaining"
text_raw\<open>\label{basic-proof-chain}\<close>

text \<open>
In both cases described for fact input until now, the facts still have been referred by names.
This can be avoided by automatically using a stated fact as input to the proof of the next
stated fact. That is called ``fact chaining''. 
\<close>

subsubsection "Automatic Update of the Current Facts"

text\<open>
Fact chaining is achieved, because Isabelle automatically updates the fact set \<open>this\<close>.
Whenever a new fact is added to the proof context, the set \<open>this\<close> is redefined to contain (only)
this fact. In particular, after every goal statement \<open>this\<close> names the new proven fact. Therefore
the fact set \<open>this\<close> is also called the ``current facts''.

Thus a linear sequence of facts can be constructed by
@{theory_text[display]
\<open>have "F\<^sub>1" `\<proof>\<^sub>1`
then have "F\<^sub>2" `\<proof>\<^sub>2`
\<dots>
then have "F\<^sub>n" `\<proof>\<^sub>n`\<close>}
Now in every \<open>proof\<^sub>i\<close> the fact \<open>F\<^sub>i\<^sub>-\<^sub>1\<close> is available as input and can be used to prove \<open>F\<^sub>i\<close>.

Chaining can be combined with explicit fact referral by a statement of the form
@{theory_text[display]
\<open>note this name\<^sub>1 \<dots> name\<^sub>n\<close>}
It sets \<open>this\<close> to the union of \<open>this\<close> and the \<open>name\<^sub>1 \<dots> name\<^sub>n\<close>, i.e., it adds the \<open>name\<^sub>1 \<dots> name\<^sub>n\<close>
to \<open>this\<close>. In this way the current facts can be extended with other facts and then chained
to the proof of the next stated fact.

The statement sequence
@{theory_text[display]
\<open>note this name\<^sub>1 \<dots> name\<^sub>n then\<close>}
can be abbreviated by the statement
@{theory_text[display]
\<open>with name\<^sub>1 \<dots> name\<^sub>n\<close>}
Like \<^theory_text>\<open>then\<close> it switches to mode \<open>proof(chain)\<close> and it inputs the union of the facts referred by 
\<open>name\<^sub>1 \<dots> name\<^sub>n\<close> together with the current facts to the proof of the following goal statement.

If a proof consists of a fact tree with several branches, every branch can be constructed this
way. Before switching to the next branch the last fact must be named, so that it can later be used
to prove the fact where the branches join. A corresponding proof pattern for two branches which
join at fact \<open>F\<close> is
@{theory_text[display]
\<open>have "F\<^sub>1\<^sub>1" `\<proof>\<^sub>1\<^sub>1`
then have "F\<^sub>1\<^sub>2" `\<proof>\<^sub>1\<^sub>2`
\<dots>
then have name\<^sub>1: "F\<^sub>1\<^sub>m" `\<proof>\<^sub>1\<^sub>m`
have "F\<^sub>2\<^sub>1" `\<proof>\<^sub>2\<^sub>1`
then have "F\<^sub>2\<^sub>2" `\<proof>\<^sub>2\<^sub>2`
\<dots>
then have "F\<^sub>2\<^sub>n" `\<proof>\<^sub>2\<^sub>n`
with name\<^sub>1 have "F" \<proof>
\<close>}
\<close>

subsubsection "Naming and Grouping Current Facts"

text \<open>
Since the fact set built by a \<^theory_text>\<open>note\<close> statement is overwritten by the next stated fact,
it is possible to give it an explicit name in addition to the name \<open>this\<close> in the form
@{theory_text[display]
\<open>note name = name\<^sub>1 \<dots> name\<^sub>n\<close>}
The \<open>name\<close> can be used later to refer to the same fact set again, when \<open>this\<close> has already been updated.
Defining such names is only possible in the \<^theory_text>\<open>note\<close> statement, not in the abbreviated forms
\<^theory_text>\<open>from\<close> and \<^theory_text>\<open>with\<close>.

The facts specified in \<^theory_text>\<open>note\<close>, \<^theory_text>\<open>from\<close>, \<^theory_text>\<open>with\<close>, and \<^theory_text>\<open>using\<close> can be grouped by separating 
them by \<^theory_text>\<open>and\<close>. Thus it is even possible to write
@{theory_text[display]
\<open>from name\<^sub>1 and \<dots> and name\<^sub>n have "prop" \<proof>\<close>}
In the case of a \<^theory_text>\<open>note\<close> statement every group can be given an additional explicit name as in
@{theory_text[display]
\<open>note name\<^sub>1 = name\<^sub>1\<^sub>1 \<dots> name\<^sub>1\<^sub>m\<^sub>1 and \<dots> and name\<^sub>n = name\<^sub>n\<^sub>1 \<dots> name\<^sub>n\<^sub>m\<^sub>n\<close>}
\<close>

subsubsection "Accessing Input Facts in a Structured Proof"

text \<open>
At the beginning of a structured proof the set name \<open>this\<close> is undefined, the name cannot be used
to refer to the input facts (which are the current facts in the enclosing proof). To access
the input facts they must be named before they are chained to the goal statement, then they
can be referenced in the subproof by that name. For example in
@{theory_text[display]
\<open>note input = this
then have "prop" \<proof>\<close>}
the input facts can be referenced by the name \<open>input\<close> in \<^theory_text>\<open>\<proof>\<close>.
\<close>

subsubsection "Exporting the Current Facts of a Nested Context"

text \<open>
At the end of a nested context (see Section~\ref{basic-proof-struct}) the current facts are
automatically exported to the enclosing context, i.e. they become available there as the fact
set named \<open>this\<close>, replacing the current facts before the nested context. This is another way
how facts from a nested context can contribute to the overall proof.

Basically, only the last fact is current at the end of a context. Arbitrary facts can be 
exported from the nested context by explicitly making them current at its end, typically using a 
\<^theory_text>\<open>note\<close> statement:
@{theory_text[display]
\<open>\<dots> { 
  have f\<^sub>1: "prop\<^sub>1" `\<proof>\<^sub>1`
  \<dots>
  have f\<^sub>n: "prop\<^sub>n" `\<proof>\<^sub>n` 
  note f\<^sub>1 \<dots> f\<^sub>n 
  } \<dots>\<close>}
Here all facts are named and the \<^theory_text>\<open>note\<close> statement makes them current by referring them by 
their names. Note, that the names are only valid in the nested context and cannot be used
to refer to the exported facts in the outer context.

The exported facts can be used in the outer context like all other current facts by directly 
chaining them to the next stated fact:
@{theory_text[display]
\<open>\<dots> { \<dots> } then have "prop" \<proof>  \<dots>\<close>}
or by naming them for later use, with the help of a \<^theory_text>\<open>note\<close> statement:
@{theory_text[display]
\<open>\<dots> { \<dots> } note name = this \<dots>\<close>}
\<close>

subsection "Assuming Facts"
text_raw\<open>\label{basic-proof-assume}\<close>

text \<open>
The Assumptions \<open>A\<^sub>1,\<dots>,A\<^sub>n\<close> of the proposition to be proven are needed as facts in the proof 
context to start the branches of the fact tree. However, they are not automatically inserted, 
that must be done explicitly.
\<close>

subsubsection "Introducing Assumed Facts"

text \<open>
An assumption is inserted in the proof context by a statement of the form
@{theory_text[display]
\<open>assume "prop"\<close>}
Several assumptions can be inserted in a single \<^theory_text>\<open>assume\<close> statement of the form
@{theory_text[display]
\<open>assume "prop\<^sub>1" \<dots> "prop\<^sub>n"\<close>}
As usual, the assumptions can be grouped by \<^theory_text>\<open>and\<close> and the groups can be named.

Like goal statements an \<^theory_text>\<open>assume\<close> statement makes the assumed facts current, i.e. it updates
the set \<open>this\<close> to contain the specified propositions as facts, so that they can be chained
to a following goal statement. This way the fact sequence \<open>A \<Longrightarrow> F\<^sub>1, F\<^sub>1 \<Longrightarrow> \<cdots>\<close> of a proof
using fact chaining can be started:
@{theory_text[display]
\<open>assume "A" 
then have "F\<^sub>1"
\<dots>
\<close>}

Alternatively, the assumed facts can be named:
@{theory_text[display]
\<open>assume name: "prop\<^sub>1" \<dots> "prop\<^sub>n"\<close>}
so that they can be referred by name in the rest of the proof. Then the fact chain can be started 
in the form
@{theory_text[display]
\<open>assume a: "A" 
from a have "F\<^sub>1"
\<dots>
\<close>}
This can be useful if the proof has several branches which all start at the same assumption.
\<close>

subsubsection "Admissible Assumed Facts"

text \<open>
In an \<^theory_text>\<open>assume\<close> statement no proof is needed, since these propositions are only ``assumed'' 
to be valid. Therefore, only the propositions occurring as assumptions in the goal 
\<open>\<lbrakk>A\<^sub>1;\<dots>;A\<^sub>n\<rbrakk> \<Longrightarrow> C\<close> to be proven are allowed here.

Actually, this condition is not checked for the \<^theory_text>\<open>assume\<close> statement, an arbitrary proposition can 
be specified by it. The condition becomes only relevant in subsequent \<^theory_text>\<open>show\<close> statements. When 
the fact proven by a show statement is tried to be unified with the conclusion of a goal, 
additionally each proposition stated in an \<^theory_text>\<open>assume\<close> statement is tested for unifying with an
assumption of the same goal. If that is not satisfied, the \<^theory_text>\<open>show\<close> statement fails. Therefore,
if a proposition is used in an \<^theory_text>\<open>assume\<close> statement which does not unify with an assumption in 
a goal, the proof cannot be completed, because all \<^theory_text>\<open>show\<close> statements will fail.
\<close>

subsubsection "Exporting Facts with Assumptions"

text\<open>
More generally, whenever a local fact \<open>F\<close> is exported from a proof context, it is combined 
with all locally assumed facts \<open>AF\<^sub>1,\<dots>,AF\<^sub>n\<close> to the derivation rule \<open>\<lbrakk>AF\<^sub>1;\<dots>;AF\<^sub>n\<rbrakk> \<Longrightarrow> F\<close>. This
reflects the intention of the local assumptions: They may have been used locally to prove \<open>F\<close> 
without knowing whether they are valid. So outside the local context \<open>F\<close> is only known to 
be valid if all the assumptions are valid.

If the fact \<open>F\<close> is itself a derivation rule \<open>\<lbrakk>A\<^sub>1;\<dots>;A\<^sub>n\<rbrakk> \<Longrightarrow> C\<close> then the locally assumed facts
are added, resulting in the exported rule \<open>\<lbrakk>AF\<^sub>1;\<dots>;AF\<^sub>n;A\<^sub>1;\<dots>;A\<^sub>n\<rbrakk> \<Longrightarrow> C\<close>.

If the fact \<open>F\<close> has been proven in a \<^theory_text>\<open>show\<close> statement it is also exported in this way, resulting
in a derivation rule. It matches with a goal if the conclusion of the exported rule unifies
with the goal conclusion and if every assumption of the exported rule unifies with an assumption
in the goal. This way of matching a rule with a goal is called ``refinement''. So the condition 
for a successful \<^theory_text>\<open>show\<close> statement can be stated as ``the exported fact must refine a goal''.
\<close>

subsubsection "Avoiding Repeated Propositions for Assumed Facts"

text\<open>
To make \<^theory_text>\<open>show\<close> statements succeed, an \<^theory_text>\<open>assume\<close> statement will usually repeat one or more 
assumptions from the proposition to be proven. This is similar to a \<^theory_text>\<open>show\<close> statement, which 
usually repeats the conclusion of that proposition. However, unlike \<open>?thesis\<close> for the conclusion, 
there is no abbreviation provided for the assumptions.

To avoid repeating propositions in \<^theory_text>\<open>assume\<close> statements, the proposition to be proven can be 
specified in the form (see Section~\ref{basic-theory-theorem})
@{theory_text[display]
\<open>theorem 
  assumes "A\<^sub>1" and \<dots> and "A\<^sub>n"
  shows "C"
  \<proof>\<close>}
This form automatically inserts the assumptions as assumed facts in the proof context.
No \<^theory_text>\<open>assume\<close> statements are needed, the assumptions need not be repeated, and the assumed 
facts are always safe for \<^theory_text>\<open>show\<close> statements.

The assumptions can still be named and referred by name in the proof. A proof can be started
at assumption \<open>A\<^sub>1\<close> in the form
@{theory_text[display]
\<open>theorem 
  assumes name\<^sub>1: "A\<^sub>1" and \<dots> and name\<^sub>n: "A\<^sub>n"
  shows "C"
  proof `method`
    from name\<^sub>1 have "F\<^sub>1" \<proof>
    \<dots>\<close>}

Additionally, the set of all assumptions specified in this form of a theorem is automatically named 
\<open>assms\<close>. Since unneeded assumptions usually do not harm in a proof, each proof branch can be 
started in the form
@{theory_text[display]
\<open>from assms have "F\<^sub>1"
\<dots>\<close>}
but it is usually clearer for the reader to specify only the relevant assumption(s) by explicit 
names.

In subproofs \<^theory_text>\<open>assume\<close> statements cannot be avoided in this way, because propositions
in goal statements cannot be specified using \<^theory_text>\<open>assumes\<close> and \<^theory_text>\<open>shows\<close>. However, goal statements 
usually specify only a fact as proposition without assumptions. Instead of assumed facts the 
subproof can either use facts provided as input, or use external facts from the enclosing proof
context by referring to them by name.
\<close>

subsubsection "Presuming Facts"

text \<open>
It is also possible to use a proposition as assumed fact which does not unify with an
assumption in a goal, but can be proven from them. In other words, the proof is started
somewhere in the middle of the fact tree, works in forward reasoning mode, and when 
it reaches the conclusion the assumed fact remains to be proven. The statement
@{theory_text[display]
\<open>presume "prop"\<close>}
inserts such a presumed fact into the proof context. 

When a fact is exported from a context with presumed facts, they do not become a part of
the exported rule. Instead, at the end of the context for each presumed fact \<open>F\<^sub>p\<close> a new goal
\<open>\<lbrakk>A\<^sub>1;\<dots>;A\<^sub>n\<rbrakk> \<Longrightarrow> F\<^sub>p\<close> is added to the enclosing goal state. So the proof has to continue after 
proving all original goals and is only finished when all such goals for presumed facts 
have been proven as well.
\<close>

subsection "Fixing Variables"
text_raw\<open>\label{basic-proof-fix}\<close>

text \<open>
Variables occurring in the proposition of a theorem can be used in the proof as well, they are
universally bound in the whole proof context, if they are not explicitly bound in the proposition,
which restricts their use to the proposition itself. Thus in
@{theory_text[display]
\<open>theorem "\<And>x::nat. x < 3 \<Longrightarrow> x < 5" \<proof>\<close>}
the variable \<open>x\<close> is restricted to the proposition and is not accessible in \<^theory_text>\<open>\<proof>\<close>, whereas in 
@{theory_text[display]
\<open>theorem "(x::nat) < 3 \<Longrightarrow> x < 5" \<proof>\<close>}
and 
@{theory_text[display]
\<open>theorem "x < 3 \<Longrightarrow> x < 5" for x::nat \<proof>\<close>}
the variable \<open>x\<close> is accessible in \<^theory_text>\<open>\<proof>\<close>.
\<close>

subsubsection "Local Variables"

text\<open>
Additional local variables can be introduced (``fixed'') in a proof context in mode \<open>proof(state)\<close>
by the statement
@{theory_text[display]
\<open>fix x\<^sub>1 \<dots> x\<^sub>n\<close>}
As usual the variables can be grouped by \<^theory_text>\<open>and\<close> and types can be specified for (some of) the groups. 

If a variable name is used in a proof context without explicitly fixing it, it either refers to a
variable in an enclosing context or in the proposition to be proven, or it is free. If it is
explicitly fixed it names a variable which is different from all variables with the same name in 
enclosing contexts and the proposition to be proven.

A fixed local variable is common to the whole local context. If it occurs in several local facts 
it always is the same variable, it is not automatically restricted to the fact, as for toplevel
theorems. Hence in
@{theory_text[display]
\<open>fix x::nat
assume a: "x < 3"
have "x < 5" \<proof>\<close>}
the \<^theory_text>\<open>\<proof>\<close> may refer to fact \<open>a\<close> because the \<open>x\<close> is the same variable in both facts.

By convention variable names are often short consisting of one or two letters, whereas constants
defined on toplevel in a theory have longer and more descriptive names. Therefore it is usually
not necessary to explicitly fix the variables in the proposition of a theorem to prevent name
clashes with constants. By contrast, in a nested proof context there may be other variables with the 
same name in enclosing contexts, therefore it is recommended to explicitly fix all local variables. 
\<close>

subsubsection "Exporting Facts with Local Variables"

text \<open>
Explicitly fixing variables in a proof context is not only important for avoiding name clashes.
If a fact is exported from a proof context, all fixed local variables are replaced by unknowns,
other variables remain unchanged. Since unification only works for unknowns, it makes a difference
whether a fact uses a local variable or a variable which origins from an enclosing context or
is free.

The proposition \<open>x < 3 \<Longrightarrow> x < 5\<close> can be proven by the statements 
@{theory_text[display]
\<open>fix y::nat
assume "y < 3"
then show "y < 5" \<proof>
\<close>}
because when the fact \<open>y < 5\<close> is exported, the assumption is added (as described in 
Section~\ref{basic-proof-assume}) and then variable \<open>y\<close> is replaced by the unknown \<open>?y\<close>
because \<open>y\<close> has been locally fixed. The result is the rule \<open>?y<3 \<Longrightarrow> ?y<5\<close> which unifies
with the proposition.

If, instead, \<open>y\<close> is not fixed, the sequence
@{theory_text[display]
\<open>assume "(y::nat) < 3"
then have "y < 5" \<proof>
\<close>}
still works and the local fact \<open>y < 5\<close> can be proven, but it cannot be used with the \<^theory_text>\<open>show\<close>
statement to prove the proposition \<open>x < 3 \<Longrightarrow> x < 5\<close>, because the exported rule is now 
\<open>y<3 \<Longrightarrow> y<5\<close> which does not unify with the proposition, it contains a different variable
instead of an unknown.
\<close>

subsection "Obtaining Variables"
text_raw\<open>\label{basic-proof-obtain}\<close>

text \<open>
Local variables may also be introduced together with a fact which allows to determine their values.
This is done using a statement of the form
@{theory_text[display]
\<open>obtain x\<^sub>1 \<dots> x\<^sub>m where "prop" \<proof>\<close>}
where \<open>prop\<close> is a proposition in inner syntax which contains the variables \<open>x\<^sub>1 \<dots> x\<^sub>m\<close>. 
Like for variables introduced by \<^theory_text>\<open>fix\<close> the variables can be grouped by \<^theory_text>\<open>and\<close> and types can be 
specified for (some of) the groups. 

The proposition usually relates the values of the new variables to values of existing variables 
(which may be local or come from the environment). In the simplest case the proposition directly 
specifies terms for the new variables, such as in
@{theory_text[display]
\<open>fix x::nat
obtain y z where "y = x + 3 \<and> z = x + 5" \<proof>\<close>}
But it is also possible to specify the values indirectly:
@{theory_text[display]
\<open>fix x::nat
obtain y z where "x = y - 3 \<and> y + z = 2*x +8" \<proof>\<close>}
Here the proposition may be considered to be an additional assumption which is added to the proof
context.
\<close>

subsubsection "Proving \<open>obtain\<close> Statements"

text\<open>
Actually, several propositions may be specified in an \<^theory_text>\<open>obtain\<close> statement:
@{theory_text[display]
\<open>obtain x\<^sub>1 \<dots> x\<^sub>m where "prop\<^sub>1" \<dots> "prop\<^sub>n" \<proof>\<close>}
The propositions may be grouped by \<^theory_text>\<open>and\<close> and the groups can be named as usual.
This \<^theory_text>\<open>obtain\<close> statement has a similar meaning as the statements
@{theory_text[display]
\<open>fix x\<^sub>1 \<dots> x\<^sub>m 
assume "prop\<^sub>1" \<dots> "prop\<^sub>n"\<close>}
but there is one important difference: the propositions in an \<^theory_text>\<open>obtain\<close> statement must be redundant
in the local proof context.

That is the reason why an \<^theory_text>\<open>obtain\<close> statement is a goal statement and includes a proof. The proof 
must prove the redundancy
of the propositions, which may be stated in the following way: if any other proposition can be 
derived from them in the local proof context it must be possible to also derive it without the
propositions. This can be stated formally as 
@{text[display]
\<open>(\<And>x\<^sub>1 \<dots> x\<^sub>m. \<lbrakk>prop\<^sub>1; \<dots>; prop\<^sub>n\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P\<close>}
which is exactly the goal to be proven for the \<^theory_text>\<open>obtain\<close> statement.

Consider the statements
@{theory_text[display]
\<open>fix x::nat
obtain y where "x = 2*y" \<proof>\<close>}
This proposition is not redundant, because it implies that \<open>x\<close> must be even. Therefore no proof
exists.

Note that after a successful proof of an \<^theory_text>\<open>obtain\<close> statement the current facts are the propositions
specified in the statement, not the proven redundancy statement. Input facts may be passed to 
\<^theory_text>\<open>obtain\<close> statements. Like for the other goal statements, they are input to the \<open>\<proof>\<close>.
\<close>

subsubsection "Exporting Facts after Obtaining Variables"

text\<open>
Unlike facts assumed by an \<^theory_text>\<open>assume\<close> statement (see Section~\ref{basic-proof-assume}) the 
propositions in an \<^theory_text>\<open>obtain\<close> statement are \<^emph>\<open>not\<close> added as assumptions when a fact \<open>F\<close> is 
exported from the local context. This is correct, since they have been proven to be redundant,
therefore they can be omitted.

However, that implies that an exported fact \<open>F\<close> may not refer to variables introduced by an
\<^theory_text>\<open>obtain\<close> statement, because the information provided by the propositions about them gets
lost during the export.
\<close>

subsection "Term Abbreviations"
text_raw\<open>\label{basic-proof-let}\<close>

text \<open>
A term abbreviation is a name for a proposition or a term in it. 
\<close>

subsubsection "Defining Term Abbreviations"

text\<open>A term abbreviation can be defined by a statement of the form
@{theory_text[display]
\<open>let ?name = "term"\<close>}
Afterwards the name is ``bound'' to the term and can be used in place of the term in 
propositions and other terms, as in:
@{theory_text[display]
\<open>let ?lhs = "2*x+3"
let ?rhs = "2*5+3"
assume "x < 5"
have "?lhs \<le> ?rhs" \<proof>\<close>}

The name \<open>?thesis\<close> (see Section~\ref{basic-proof-forwstep}) is a term abbreviation of this
kind.

A \<^theory_text>\<open>let\<close> statement can define several term abbreviations in the form
@{theory_text[display]
\<open>let ?name\<^sub>1 = "term\<^sub>1" and \<dots> and ?name\<^sub>n = "term\<^sub>n"\<close>}

A \<^theory_text>\<open>let\<close> statement can occur everywhere in mode \<open>proof(state)\<close>. However, it does not preserve
the current facts, the fact set \<open>this\<close> becomes undefined by it. 
\<close>

subsubsection "Pattern Matching"

text \<open>
Note that term abbreviations have the form of ``unknowns'' (see Section~\ref{basic-theory-theorem}),
although they are defined (``bound''). The reason is that they are actually defined by unification.

The more general form of a \<^theory_text>\<open>let\<close> statement is
@{theory_text[display]
\<open>let "pattern" = "term"\<close>}
where \<open>pattern\<close> is a term which may contain unbound unknowns. As usual, if the pattern consists of
a single unknown, the quotes may be omitted. The \<^theory_text>\<open>let\<close> statement unifies \<open>pattern\<close>
and \<open>term\<close>, i.e., it determines terms to substitute for the unknowns, so that the pattern becomes
syntactically equal to \<open>term\<close>. If that is not possible, an error is signaled, otherwise the
unknowns are bound to the substituting terms. Note that the equals sign belongs to the outer syntax,
therefore both the pattern and the term must be quoted separately.

The \<^theory_text>\<open>let\<close> statement
@{theory_text[display]
\<open>let "?lhs \<le> ?rhs" = "2*x+3 \<le> 2*5+3"\<close>}
binds the unknowns to the same terms as the two \<^theory_text>\<open>let\<close> statements above.

The term may contain unknowns which are already bound. They are substituted 
by their bound terms before the pattern matching is performed. Thus the term
can be constructed with the help of abbreviation which have been defined previously. A useful
example is matching a pattern with \<open>?thesis\<close>:
@{theory_text[display]
\<open>theorem "x < 5 \<Longrightarrow> 2*x+3 \<le> 2*5+3" 
proof `method` 
  let "?lhs \<le> ?rhs" = ?thesis
  \<dots>\<close>}
to reuse parts of the conclusion in the proof.

Note that the unknowns are only bound at the end of the whole \<^theory_text>\<open>let\<close> statement. In the form
@{theory_text[display]
\<open>let "pattern\<^sub>1" = "term\<^sub>1" and \<dots> and "pattern\<^sub>n" = "term\<^sub>n"\<close>}
the unknowns in \<open>pattern\<^sub>i\<close> cannot be used to build \<open>term\<^sub>i\<^sub>+\<^sub>1\<close> because they are not yet bound.
In contrast, in the sequence of \<^theory_text>\<open>let\<close> statements
@{theory_text[display]
\<open>let "pattern\<^sub>1" = "term\<^sub>1" 
 \<dots> 
let "pattern\<^sub>n" = "term\<^sub>n"\<close>}
the unknowns in \<open>pattern\<^sub>i\<close> can be used to build \<open>term\<^sub>i\<^sub>+\<^sub>1\<close> because they are already bound.

If a bound unknown occurs in the pattern its bound term is ignored and the unknown is rebound
according to the pattern matching. In particular, it does not imply that the old and new bound
terms must be equal, they are completely independent.

If a part of the term is irrelevant and need not be bound the dummy unknown ``\_'' (underscore)
can be used to match it in the pattern without binding an unknown to it:
@{theory_text[display]
\<open>let "_ \<le> ?rhs" = "2*x+3 \<le> 2*5+3"\<close>}
will only bind \<open>?rhs\<close> to the term on the righthand side.

If the term internally binds variables which are used in a subterm, the subterm cannot be matched
separately by an unknown because then the variable bindings would be lost. Thus the statement
@{theory_text[display]
\<open>let "\<lambda>x. ?t" = "\<lambda>x. x+1"\<close>} 
will fail to bind \<open>?t\<close> to \<open>x+1\<close> whereas
@{theory_text[display]
\<open>let "\<lambda>x. x+?t" = "\<lambda>x. x+1"\<close>} 
will successfully bind \<open>?t\<close> to \<open>1\<close> since the bound variable \<open>x\<close> does not occur in it.
\<close>

subsection "Accumulating Facts"
text_raw\<open>\label{basic-proof-moreover}\<close>

text \<open>
Instead of giving individual names to facts in the proof context, facts can be collected in
named fact sets. Isabelle supports the specific fact set named \<open>calculation\<close> and provides
statements for managing it.

The fact set \<open>calculation\<close> is intended to accumulate current facts for later use. Therefore
it is typically initialized by the statement
@{theory_text[display]
\<open>note calculation = this\<close>}
and afterwards it is extended by several statements
@{theory_text[display]
\<open>note calculation = calculation this\<close>}
After the last extension the facts in the set are chained to the next proof:
@{theory_text[display]
\<open>note calculation = calculation this then have \<dots>\<close>}
\<close>

subsubsection "Support for Fact Accumulation"

text\<open>
Isabelle supports this management of \<open>calculation\<close> with two statements. The statement 
@{theory_text[display]
\<open>moreover\<close>}
is equivalent to \<^theory_text>\<open>note calculation = this\<close> when it occurs the first time in a context, 
afterwards it behaves like \<^theory_text>\<open>note calculation = calculation this\<close> but without making 
\<open>calculation\<close> current, instead, it leaves the current fact(s) unchanged. The statement
@{theory_text[display]
\<open>ultimately\<close>}
is equivalent to \<^theory_text>\<open>note calculation = calculation this then\<close>, i.e., it adds the current 
facts to the set, makes the set current, and chains it to the next goal statement.

Due to the block structure of nested proofs, the \<open>calculation\<close> set can be reused in nested
contexts without affecting the set in the enclosing context. The first occurrence of 
\<^theory_text>\<open>moreover\<close> in the nested context initializes a fresh local \<open>calculation\<close> set. Therefore
fact accumulation is always local to the current proof context.
\<close>

subsubsection "Accumulating Facts in a Nested Context"

text\<open>
Fact accumulation can be used for collecting the facts in a nested context for export
(see Section~\ref{basic-proof-chain}) without using explicit names for them:
@{theory_text[display]
\<open>\<dots> { 
  have "prop\<^sub>1" `\<proof>\<^sub>1` 
  moreover have "prop\<^sub>2" `\<proof>\<^sub>2`
  \<dots>
  moreover have "prop\<^sub>n" `\<proof>\<^sub>n` 
  moreover note calculation 
  } \<dots>\<close>}
\<close>

subsubsection "Accumulating Facts for Joining Branches"

text\<open>
Fact accumulation can also be used for collecting the facts at the end of joined fact branches
in a proof and inputting them to the joining step. A corresponding proof pattern for two branches which
join at fact \<open>F\<close> is
@{theory_text[display]
\<open>have "F\<^sub>1\<^sub>1" `\<proof>\<^sub>1\<^sub>1`
then have "F\<^sub>1\<^sub>2" `\<proof>\<^sub>1\<^sub>2`
\<dots>
then have "F\<^sub>1\<^sub>m" `\<proof>\<^sub>1\<^sub>m`
moreover have "F\<^sub>2\<^sub>1" `\<proof>\<^sub>2\<^sub>1`
then have "F\<^sub>2\<^sub>2" `\<proof>\<^sub>2\<^sub>2`
\<dots>
then have "F\<^sub>2\<^sub>n" `\<proof>\<^sub>2\<^sub>n`
ultimately have "F" \<proof>
\<close>}
The \<^theory_text>\<open>moreover\<close> statement starts the second branch and saves the fact \<open>F\<^sub>1\<^sub>m\<close> to \<open>calculation\<close>.
The \<^theory_text>\<open>ultimately\<close> statement saves the fact \<open>F\<^sub>2\<^sub>n\<close> to \<open>calculation\<close> and then inputs the set to
the proof of \<open>F\<close>. 

Note that \<^theory_text>\<open>moreover\<close> does not chain the current facts to the following goal statement.

Using nested contexts sub-branches can be constructed and joined in the same way.
\<close>

subsection "Equational Reasoning"
text_raw\<open>\label{basic-proof-equational}\<close>

text \<open>
Often informal proofs on paper are written in the style
@{text[display]
\<open>2*(x+3) = 2*x+6 \<le> 3*x+6 < 3*x+9 = 3*(x+3)\<close>}
to derive the fact \<open>2*(x+3) < 3*(x+3)\<close>. Note that the formula shown above is not a wellformed 
proposition because of several occurrences of the toplevel relation symbols \<open>=\<close>, \<open>\<le>\<close> and \<open><\<close>. 
Instead, the formula is meant as an abbreviated notation of the fact sequence
@{text[display]
\<open>2*(x+3) = 2*x+6, 2*x+6 \<le> 3*x+6, 3*x+6 < 3*x+9, 3*x+9 = 3*(x+3)\<close>}
which sketches a proof for \<open>2*(x+3) < 3*(x+3)\<close>. This way of constructing a proof is called
``equational reasoning'' which is a specific form of forward reasoning.
\<close>

subsubsection "Transitivity Rules"

text\<open>
The full proof needs additional facts which must be inserted into the sequence. From the first
two facts the fact \<open>2*(x+3) \<le> 3*x+6\<close> is derived, then with the third fact the fact 
\<open>2*(x+3) < 3*x+9\<close> is derived, and finally with the fourth fact the conclusion \<open>2*(x+3) < 3*(x+3)\<close>
is reached. The general pattern of these additional derivations can be stated as the derivation
rules
\<open>\<lbrakk>a = b; b \<le> c\<rbrakk> \<Longrightarrow> a \<le> c\<close>, \<open>\<lbrakk>a \<le> b; b < c\<rbrakk> \<Longrightarrow> a < c\<close>, and \<open>\<lbrakk>a < b; b = c\<rbrakk> \<Longrightarrow> a < c\<close>.

Rules of this form are called ``transitivity rules''. They are valid for relations such as equality,
equivalence, orderings, and combinations thereof.

This leads to the general form of a proof constructed by equational reasoning: every forward 
reasoning step starts at a fact \<open>F\<^sub>i\<close> of the form \<open>a r b\<close> where \<open>r\<close> is a relation symbol. It
proves an intermediate fact \<open>H\<^sub>i\<close> of the form \<open>b r c\<close> where \<open>r\<close> is the same or another relation
symbol and uses a transitivity rule to prove the fact \<open>F\<^sub>i\<^sub>+\<^sub>1\<close> which is \<open>a r c\<close>. In this way it
constructs a linear sequence of facts which leads to the conclusion. 

The intermediate facts \<open>H\<^sub>i\<close> are usually proven from assumtions or external facts, or they may have
a more complex proof which forms an own fact branch which ends at \<open>H\<^sub>i\<close> and is joined with the
main branch at \<open>F\<^sub>i\<^sub>+\<^sub>1\<close> with the help of the transitivity rule.
\<close>

subsubsection "Support for Equational Reasoning"

text \<open>
Isabelle supports equational reasoning in the following form. It provides the statement
@{theory_text[display]
\<open>also\<close>}
which expects that the set \<open>calculation\<close> contains the fact \<open>F\<^sub>i\<close> and the current fact
\<open>this\<close> is the fact \<open>H\<^sub>i\<close>. It automatically selects an adequate transitivity rule, uses it to
derive the fact \<open>F\<^sub>i\<^sub>+\<^sub>1\<close> and replaces \<open>F\<^sub>i\<close> in \<open>calculation\<close> by it. Upon its first use in a proof
context \<^theory_text>\<open>also\<close> simply stores the current fact \<open>this\<close> in \<open>calculation\<close>. The statement
@{theory_text[display]
\<open>finally\<close>}
behaves in the same way but additionally makes the resulting fact \<open>F\<^sub>i\<^sub>+\<^sub>1\<close> current, i.e., puts it
into the set \<open>this\<close>, and chains it into the next goal statement. In other words, \<^theory_text>\<open>finally\<close> is 
equivalent to \<^theory_text>\<open>also from calculation\<close>.

Note that \<^theory_text>\<open>also\<close> behaves like \<^theory_text>\<open>moreover\<close> and \<^theory_text>\<open>finally\<close> behaves like \<^theory_text>\<open>ultimately\<close>, both with 
additional application of the transitivity rule.

Additionally, Isabelle automatically maintains the term abbreviation \<open>\<dots>\<close> (which is the 
three-dot-symbol available for input in the Symbols panel (see ~Section~\ref{system-jedit-symbols})
of the interactive editor in tab 
``Punctuation'') for the term on the right hand side of the current fact. Together, the
example equational reasoning proof from above can be written
@{theory_text[display]
\<open>have "2*(x+3) = 2*x+6" \<proof>
also have "\<dots> \<le> 3*x+6" \<proof>
also have "\<dots> < 3*x+9" \<proof>
also have "\<dots> = 3*(x+3)" \<proof>
finally show ?thesis \<proof>\<close>}
where \<open>?thesis\<close> abbreviates the conclusion \<open>2*(x+3) < 3*(x+3)\<close>. This form is quite close to
the informal paper style of the proof.
\<close>

subsubsection "Determining Transitivity Rules"

text\<open>
To automatically determine the transitivity rule used by \<^theory_text>\<open>also\<close> or \<^theory_text>\<open>finally\<close>, Isabelle
maintains the dynamic fact set (see Section~\ref{basic-theory-theorem}) named \<open>trans\<close>.
It selects a rule from that set according to the relation symbols used in the facts in 
\<open>calculation\<close> and \<open>this\<close>.

A transitivity rule which is not in \<open>trans\<close> can be explicitly specified by name in the
form
@{theory_text[display]
\<open>also (name)
finally (name)\<close>}
\<close>

section "Proof Methods"
text_raw\<open>\label{basic-methods}\<close>

text \<open>
The basic building blocks of Isabelle proofs are the proof methods which modify the goal state.
If there are several goals in the goal state it depends on the specific method which goals 
are affected by it. In most cases only the first goal is affected.
\<close>

subsection "The empty Method"
text_raw\<open>\label{basic-methods-empty}\<close>

text\<open>
The empty method is denoted by a single minus sign
@{theory_text[display]
\<open>-\<close>}
If no input facts are passed to it, it does nothing, it does not alter the goal state.

Otherwise it affects all goals by inserting the input facts as assumptions after the existing
assumptions. If the input facts are \<open>F\<^sub>1,\<dots>,F\<^sub>m\<close> a goal of the form \<open>\<lbrakk>A\<^sub>1;\<dots>;A\<^sub>n\<rbrakk> \<Longrightarrow> C\<close> is replaced
by the goal \<open>\<lbrakk>A\<^sub>1;\<dots>;A\<^sub>n;F\<^sub>1,\<dots>,F\<^sub>m\<rbrakk> \<Longrightarrow> C\<close>. The reason for this behavior will be explained below.

The empty method is useful at the beginning of a structured proof of the form
@{theory_text[display]
\<open>proof method FS\<^sub>1 \<dots> FS\<^sub>n qed\<close>}
If the forward reasoning steps \<open>FS\<^sub>1 \<dots> FS\<^sub>n\<close> shall process the unmodified original goal the 
empty method must be specified for \<open>method\<close>, thus the structured proof becomes
@{theory_text[display]
\<open>proof - FS\<^sub>1 \<dots> FS\<^sub>n qed\<close>}

Note that it is possible to omit the \<open>method\<close> completely, but then it defaults to the method
named \<open>standard\<close> which alters the goal state (see below).
\<close>

subsection "Rule Application"
text_raw\<open>\label{basic-methods-rule}\<close>

text \<open>
As described in Section~\ref{basic-proof-proc} the basic step in the construction of a proof
is to establish the connection between a fact \<open>F\<^sub>i\<close> and a fact \<open>F\<^sub>i\<^sub>+\<^sub>1\<close> in the fact sequence. Assume
that there is already a valid derivation rule \<open>RA\<^sub>i \<Longrightarrow> RC\<^sub>i\<close> named \<open>r\<^sub>i\<close> where \<open>RA\<^sub>i\<close> unifies with 
\<open>F\<^sub>i\<close> and \<open>RC\<^sub>i\<close> unifies with \<open>F\<^sub>i\<^sub>+\<^sub>1\<close>. Then the connection can be established by applying that rule.
\<close>

subsubsection "The \<open>rule\<close> Method"

text\<open>
A rule is applied by the method
@{theory_text[display]
\<open>rule name\<close>}
where \<open>name\<close> is the name of a valid rule. The method only affects the first goal. If that goal
has the form \<open>\<lbrakk>A\<^sub>1;\<dots>;A\<^sub>n\<rbrakk> \<Longrightarrow> C\<close> and the rule referred by \<open>name\<close> has the form \<open>\<lbrakk>RA\<^sub>1;\<dots>;RA\<^sub>m\<rbrakk> \<Longrightarrow> RC\<close> 
the method first unifies \<open>RC\<close> with the goal conclusion \<open>C\<close>. That yields the specialized rule
\<open>\<lbrakk>RA\<^sub>1';\<dots>;RA\<^sub>m'\<rbrakk> \<Longrightarrow> RC'\<close> where \<open>RC'\<close> is syntactically equal to \<open>C\<close> and every \<open>RA\<^sub>j'\<close> results from
\<open>RA\<^sub>j\<close> by substituting unknowns by the same terms as in \<open>RC'\<close>. Note that the goal normally does
not contain unknowns, therefore \<open>C\<close> is not modified by the unification. If the unification fails 
the method cannot be executed on the goal state and an error is signaled. Otherwise the method 
replaces the goal by the \<open>m\<close> new goals \<open>\<lbrakk>A\<^sub>1;\<dots>;A\<^sub>n\<rbrakk> \<Longrightarrow> RA\<^sub>j'\<close>.

If the rule has the form \<open>RA \<Longrightarrow> RC\<close> with only one assumption the method replaces the goal by
the single new goal \<open>\<lbrakk>A\<^sub>1;\<dots>;A\<^sub>n\<rbrakk> \<Longrightarrow> RA'\<close>. If the rule is a formula \<open>RC\<close> without any
assumptions the method removes the goal without introducing a new goal.
\<close>

subsubsection "Using the \<open>rule\<close> Method for Backward Reasoning Steps"

text\<open>
Assume that during a proof as described in Section~\ref{basic-proof-proc} the intermediate 
fact sequence \<open>F\<^sub>i\<^sub>+\<^sub>1 \<Longrightarrow> \<cdots> \<Longrightarrow> F\<^sub>n\<close> has 
already been constructed by backward reasoning and the current goal is \<open>F\<^sub>1 \<Longrightarrow> F\<^sub>i\<^sub>+\<^sub>1\<close>. The
backward reasoning step
@{theory_text[display]
\<open>apply (rule r\<^sub>i)\<close>}
will replace that goal by \<open>F\<^sub>1 \<Longrightarrow> F\<^sub>i\<close> and thus extend the fact sequence to \<open>F\<^sub>i \<Longrightarrow> \<cdots> \<Longrightarrow> F\<^sub>n\<close>. 
The fact \<open>F\<^sub>i\<close> is the specialized assumption \<open>RA\<^sub>i'\<close> constructed by the method from
the assumption \<open>RA\<^sub>i\<close> of rule \<open>r\<^sub>i\<close>.

Therefore the fact sequence \<open>F\<^sub>1 \<Longrightarrow> \<cdots> \<Longrightarrow> F\<^sub>n\<close> of the complete proof can be 
constructed by the proof script consisting of the backward reasoning steps
@{theory_text[display]
\<open>apply (rule `r\<^sub>n\<^sub>-\<^sub>1`)
\<dots>
apply(rule r\<^sub>1)\<close>} 

Note however, that this proof
script does not complete the proof, since it results in the goal \<open>F\<^sub>1 \<Longrightarrow> F\<^sub>1\<close>. The proof method
@{theory_text[display]
\<open>assumption\<close>}
must be used to process it. The method only affects the first goal. If that goal
has the form \<open>\<lbrakk>A\<^sub>1;\<dots>;A\<^sub>n\<rbrakk> \<Longrightarrow> C\<close> and one assumption \<open>A\<^sub>i\<close> is syntactically equal to \<open>C\<close> the
method removes the goal, otherwise an error is signaled.

Together, the full proof script has the form
@{theory_text[display]
\<open>apply (rule `r\<^sub>n\<^sub>-\<^sub>1`)
\<dots>
apply(rule r\<^sub>1)
apply(assumption)
done\<close>}

If the example from Section~\ref{basic-proof-proc} is proven this way the theorem is written
together with its proof as
@{theory_text[display]
\<open>theorem "x < 5 \<Longrightarrow> 2*x+3 \<le> 2*5 + 3" for x :: nat
  apply(rule example2)
  apply(rule example1)
  apply(assumption)
  done
\<close>}

Note that the assumption \<open>A\<close> of the initial goal must be reached exactly by the sequence of rule
applications. If it is replaced in the example by the stronger assumption \<open>x < 3\<close> the rule
applications will lead to the goal \<open>x < 3 \<Longrightarrow> x < 5\<close> which is trivial for the human reader
but not applicable to the \<^theory_text>\<open>assumption\<close> method.
\<close>

subsubsection "Using the \<open>rule\<close> Method for Forward Reasoning Steps"

text\<open>
Assume that during a proof as described in Section~\ref{basic-proof-proc} the intermediate 
fact sequence \<open>F\<^sub>1 \<Longrightarrow> \<cdots> \<Longrightarrow> F\<^sub>i\<close> has 
already been constructed by forward reasoning, so that the next step is to state fact
\<open>F\<^sub>i\<^sub>+\<^sub>1\<close> and prove it. Using method \<^theory_text>\<open>rule\<close> the step can be started by
@{theory_text[display]
\<open>have "F\<^sub>i\<^sub>+\<^sub>1" proof (rule r\<^sub>i)\<close>}
The goal of this subproof is simply \<open>F\<^sub>i\<^sub>+\<^sub>1\<close>, so applying the \<^theory_text>\<open>rule\<close> method with \<open>r\<^sub>i\<close> will result
in the new goal \<open>RA\<^sub>i'\<close> which is \<open>F\<^sub>i\<close>, as above. The subproof is not finished, since its goal state 
is not empty. But the goal is an already known fact. The proof method
@{theory_text[display]
\<open>fact name\<close>}
can be used to remove that goal. The method only affects the first goal. If the fact referred by
\<open>name\<close> unifies with it, the goal is removed, otherwise an error is signaled.

Using this method the forward reasoning step can be completed as
@{theory_text[display]
\<open>have "F\<^sub>i\<^sub>+\<^sub>1" proof (rule r\<^sub>i) qed (fact f\<^sub>i)\<close>}
if \<open>F\<^sub>i\<close> has been named \<open>f\<^sub>i\<close>. This can be abbreviated (see Section~\ref{basic-proof-struct}) to
@{theory_text[display]
\<open>have "F\<^sub>i\<^sub>+\<^sub>1" by (rule r\<^sub>i) (fact f\<^sub>i)\<close>}

Therefore the fact sequence \<open>F\<^sub>1 \<Longrightarrow> \<cdots> \<Longrightarrow> F\<^sub>n\<close> of the complete proof can be 
constructed by the structured proof of the form
@{theory_text[display]
\<open>proof -
assume f\<^sub>1: "F\<^sub>1"
have f\<^sub>2: "F\<^sub>2" by (rule r\<^sub>1) (fact f\<^sub>1)
\<dots>
have `f\<^sub>n\<^sub>-\<^sub>1`: "F\<^sub>n\<^sub>-\<^sub>1" by (rule `r\<^sub>n\<^sub>-\<^sub>2`) (fact `f\<^sub>n\<^sub>-\<^sub>2`)
show "F\<^sub>n" by (rule `r\<^sub>n\<^sub>-\<^sub>1`) (fact `f\<^sub>n\<^sub>-\<^sub>1`)
qed\<close>}
where the last fact \<open>F\<^sub>n\<close> is usually the conclusion \<open>C\<close> and can be specified as \<open>?thesis\<close>.

If the example from Section~\ref{basic-proof-proc} is proven this way the theorem is written
together with its proof as
@{theory_text[display]
\<open>theorem "x < 5 \<Longrightarrow> 2*x+3 \<le> 2*5 + 3" for x :: nat
proof -
  assume f\<^sub>1: "x < 5"
  have f\<^sub>2: "2*x \<le> 2*5" by (rule example1) (fact f\<^sub>1)
  show ?thesis by (rule example2) (fact f\<^sub>2)
qed
\<close>}

The \<open>fact\<close> method can be specified in the form
@{theory_text[display]
\<open>fact\<close>}
without naming the fact to be used. Then it selects a fact automatically. It uses the first
fact from the proof context which unifies with the goal. If there is no such fact in the 
proof context an error is signaled.

Thus the example can be written without naming the facts as
@{theory_text[display]
\<open>theorem "x < 5 \<Longrightarrow> 2*x+3 \<le> 2*5 + 3" for x :: nat
proof -
  assume "x < 5"
  have "2*x \<le> 2*5" by (rule example1) fact
  show ?thesis by (rule example2) fact
qed
\<close>}

\<close>

subsubsection "Input Facts for the \<open>rule\<close> Method"

text\<open>
If input facts \<open>F\<^sub>1, \<dots>, F\<^sub>n\<close> are passed to the \<open>rule\<close> method, they are used to remove assumptions 
from the rule applied by the method. If the rule has the form \<open>\<lbrakk>RA\<^sub>1;\<dots>;RA\<^sub>n\<^sub>+\<^sub>m\<rbrakk> \<Longrightarrow> RC\<close> and
every fact \<open>F\<^sub>i\<close> unifies with assumption \<open>RA\<^sub>i\<close> the first \<open>n\<close> assumptions are removed and the
rule becomes \<open>\<lbrakk>RA\<^sub>n\<^sub>+\<^sub>1;\<dots>;RA\<^sub>n\<^sub>+\<^sub>m\<rbrakk> \<Longrightarrow> RC\<close>. Then it is applied to the first goal in the usual way.
If there are more facts than assumptions or if a fact does not unify, an error is signaled.

This allows to establish the connection from a fact \<open>F\<^sub>i\<close> to \<open>F\<^sub>i\<^sub>+\<^sub>1\<close> in a fact chain by a
forward reasoning step of the form
@{theory_text[display]
\<open>from f\<^sub>i have "F\<^sub>i\<^sub>+\<^sub>1" by (rule r\<^sub>i)\<close>}
where \<open>f\<^sub>i\<close> names the fact \<open>F\<^sub>i\<close>. When it is input to the goal statement it is passed to
the \<^theory_text>\<open>rule\<close> method and removes the assumption from the applied rule \<open>RA\<^sub>i \<Longrightarrow> RC\<^sub>i\<close>, resulting
in the assumption-less ``rule'' \<open>RC\<^sub>i\<close>. When it is applied to the goal \<open>F\<^sub>i\<^sub>+\<^sub>1\<close> it unifies and
removes the goal, thus the subproof is complete.

For the fact sequence chaining can be used to write a structured proof without naming the facts:
@{theory_text[display]
\<open>proof -
assume "F\<^sub>1"
then have "F\<^sub>2" by (rule r\<^sub>1)
\<dots>
then have "F\<^sub>n\<^sub>-\<^sub>1" by (rule `r\<^sub>n\<^sub>-\<^sub>2`)
then show "F\<^sub>n" by (rule `r\<^sub>n\<^sub>-\<^sub>1`)
qed\<close>}

If the example from Section~\ref{basic-proof-proc} is proven this way the theorem is written
together with its proof as
@{theory_text[display]
\<open>theorem "x < 5 \<Longrightarrow> 2*x+3 \<le> 2*5 + 3" for x :: nat
proof -
  assume "x < 5"
  then have "2*x \<le> 2*5" by (rule example1)
  then show ?thesis by (rule example2)
qed
\<close>}
\<close>

subsubsection "The Method \<open>this\<close>"

text\<open>
Rule application can also be done by the method
@{theory_text[display]
\<open>this\<close>}
Instead of applying a named method, it applies the input fact as rule to the first goal.

If several input facts are given, the method applies them exactly in the given order. Therefore
the fact sequence can also be constructed by a structured proof of the form:
@{theory_text[display]
\<open>proof -
assume "F\<^sub>1"
with r\<^sub>1 have "F\<^sub>2" by this
\<dots>
with `r\<^sub>n\<^sub>-\<^sub>2` have "F\<^sub>n\<^sub>-\<^sub>1" by this
with `r\<^sub>n\<^sub>-\<^sub>1` show "F\<^sub>n" by this
qed\<close>}
The \<^theory_text>\<open>with\<close> statement inserts the explicitly named facts \<^emph>\<open>before\<close> the current facts. 
Therefore every goal statement for \<open>F\<^sub>i\<close> gets as input the rule \<open>r\<^sub>i\<^sub>-\<^sub>1\<close> followed by the 
chained fact \<open>F\<^sub>i\<^sub>-\<^sub>1\<close>. The method \<open>this\<close> first applies the rule which replaces the goal
by \<open>F\<^sub>i\<^sub>-\<^sub>1\<close>. Then it applies the fact \<open>F\<^sub>i\<^sub>-\<^sub>1\<close> as rule to this goal which removes it and finishes
the subproof.

The proof
@{theory_text[display]
\<open>by this\<close>}
can be abbreviated by \<open>.\<close> (a single dot).

Therefore the example from Section~\ref{basic-proof-proc} can also be proven in the form
@{theory_text[display]
\<open>theorem "x < 5 \<Longrightarrow> 2*x+3 \<le> 2*5 + 3" for x :: nat
proof -
  assume "x < 5"
  with example1 have "2*x \<le> 2*5" .
  with example2 show ?thesis .
qed
\<close>}
\<close>

subsubsection "Adding Input Facts to the Goal"

text\<open>
Another way of using the previous fact \<open>F\<^sub>i\<close> in the proof of \<open>F\<^sub>i\<^sub>+\<^sub>1\<close> is to add it as assumption
to the goal. That is what the empty method does (see Section~\ref{basic-methods-empty}) if 
\<open>F\<^sub>i\<close> is passed as input. 

Thus the forward reasoning step can be written in the form
@{theory_text[display]
\<open>from f\<^sub>i have "F\<^sub>i\<^sub>+\<^sub>1" 
proof - 
  assume "F\<^sub>i" 
  then show ?thesis by (rule r\<^sub>i) 
qed\<close>}
The empty method \<open>-\<close> replaces the goal \<open>F\<^sub>i\<^sub>+\<^sub>1\<close> by the goal \<open>F\<^sub>i \<Longrightarrow> F\<^sub>i\<^sub>+\<^sub>1\<close> which is then proven 
by a forward reasoning step.

Of course this is much longer than the proof using the \<open>rule\<close> method immediately. But it shows
generally how the step from \<open>F\<^sub>i\<close> to \<open>F\<^sub>i\<^sub>+\<^sub>1\<close> can be established using an arbitrary structured proof.
That can be useful if no direct derivation rule \<open>r\<^sub>i\<close> is available.
\<close>

subsubsection "Automatic Rule Selection"

text\<open>
The \<open>rule\<close> method can be specified in the form
@{theory_text[display]
\<open>rule\<close>}
without naming the rule to be applied. Then it selects a rule automatically. It uses the first
rule from the dynamic fact set \<open>intro\<close> for which the conclusion unifies with the goal conclusion.
If there is no such rule in the set an error is signaled.

If the rules \<open>example1\<close> and \<open>example2\<close> would be in the \<open>intro\<close> set, the example proof could
be written as
@{theory_text[display]
\<open>theorem "x < 5 \<Longrightarrow> 2*x+3 \<le> 2*5 + 3" for x :: nat
proof -
  assume "x < 5"
  then have "2*x \<le> 2*5" by rule
  then show ?thesis by rule
qed
\<close>}

However, the set \<open>intro\<close> is intended by Isabelle for a specific kind of rules called 
``introduction rules''. In such a rule the toplevel operator of the conclusion does not
occur in any assumption, hence it is ``introduced'' by the rule. When an introduction rule
is applied backwards, the operator is removed from the goal. This can be iterated to 
``deconstruct'' the goal, some proofs can be written using this technique, however, the 
content of the set must be designed very carefully to not run into cycles.

Since in the rule \<open>example2\<close> the toplevel operator \<open>\<le>\<close> occurs in the assumption it is not 
an introduction rule and should not be added to \<open>intro\<close>. Rule \<open>example1\<close> is an introduction
rule but would interfere with predefined rules in the set. 
\<close>

subsubsection "The \<open>standard\<close> Method"

text\<open>
The method
@{theory_text[display]
\<open>standard\<close>}
is a method alias which can be varied for different Isabelle applications. Usually it is
an alias for the \<open>rule\<close> method.

The \<open>standard\<close> method is the default, if no method is specified as the initial step in a 
structured proof. Thus 
@{theory_text[display]
\<open>proof FS\<^sub>1 \<dots> FS\<^sub>n qed\<close>}
is an abbreviation for
@{theory_text[display]
\<open>proof standard FS\<^sub>1 \<dots> FS\<^sub>n qed\<close>}

Note that the \<open>standard\<close> method will usually affect the goal by applying an introduction
rule to it. That may be useful in some cases, but it has to be taken into account when writing
the forward reasoning steps of the proof. For example, in Isabelle HOL there is an introduction
rule in \<open>intro\<close> which splits a logical conjunction into two subgoals (see 
Section~\ref{hol-types-bool}). Therefore the proof of a conjunction \<open>P \<and> Q\<close> can be written
@{theory_text[display]
\<open>proof 
show P \<proof>
show Q \<proof>
qed\<close>}
because the goal is split by the \<open>standard\<close> method. If the empty method is used instead, the
proof has to be of the form
@{theory_text[display]
\<open>proof -
show "P \<and> Q" \<proof>
qed\<close>}
because the goal is not modified.

In the abbreviated form \<^theory_text>\<open>by method\<close> of a structured proof the method cannot be omitted, but
the proof \<^theory_text>\<open>by standard\<close> can be abbreviated to
@{theory_text[display]
\<open>..\<close>}
(two dots). It can be used as complete proof for a proposition which can be proven by a single
automatic rule application. Hence, if the rules \<open>example1\<close> and \<open>example2\<close> would be in the \<open>intro\<close> 
set, the example proof could be further abbreviated as
@{theory_text[display]
\<open>theorem "x < 5 \<Longrightarrow> 2*x+3 \<le> 2*5 + 3" for x :: nat
proof -
  assume "x < 5"
  then have "2*x \<le> 2*5" ..
  then show ?thesis ..
qed
\<close>}
\<close>

subsection "Composed Proof Methods"
text_raw\<open>\label{basic-methods-composed}\<close>

text \<open>
Proof methods can be composed from simpler methods with the help of ``method expressions''.
A method expression has one of the following forms:
 \<^item> \<open>m\<^sub>1, \<dots>, m\<^sub>n\<close> : a sequence of methods which are applied in their order,
 \<^item> \<open>m\<^sub>1; \<dots>; m\<^sub>n\<close> : a sequence of methods where each is applied to the goals created by the previous method,
 \<^item> \<open>m\<^sub>1| \<dots>| m\<^sub>n\<close> : a sequence of methods where only the first applicable method is applied,
 \<^item> \<open>m[n]\<close> : the method \<open>m\<close> is applied to the first \<open>n\<close> goals,
 \<^item> \<open>m?\<close> : the method \<open>m\<close> is applied if it is applicable,
 \<^item> \<open>m+\<close> : the method \<open>m\<close> is applied once and then repeated as long as it is applicable.

Parentheses are used to structure and nest composed methods.

Composed methods can be used to combine backward reasoning steps to a single step. Using composed 
methods the example backward reasoning proof from Section~\ref{basic-methods-rule} can be written 
as
@{theory_text[display]
\<open>theorem "x < 5 \<Longrightarrow> 2*x+3 \<le> 2*5 + 3" for x :: nat
  apply(rule example2,rule example1,assumption)
  done
\<close>}

In particular, it is possible to apply an arbitrarily complex backward reasoning step as the first 
method in a structured proof. Using composed methods the first example forward reasoning proof can 
be written
@{theory_text[display]
\<open>theorem "x < 5 \<Longrightarrow> 2*x+3 \<le> 2*5 + 3" for x :: nat
proof -
  assume "x < 5"
  have "2*x \<le> 2*5" by (rule example1,fact)
  show ?thesis by (rule example2,fact)
qed
\<close>}
\<close>

subsection "The Simplifier"
text_raw\<open>\label{basic-methods-simp}\<close>

text \<open>
A common proof technique is ``rewriting''. If it is known that a term \<open>a\<close> is equal to a term
\<open>b\<close>, some occurrences of \<open>a\<close> in a proposition can be replaced by \<open>b\<close> without changing the 
validity of the proposition.

Equality of two terms \<open>a\<close> and \<open>b\<close> can be expressed by the proposition \<open>a = b\<close>. If that 
proposition has been proven to be valid, i.e., is a fact, \<open>a\<close> can be substituted by \<open>b\<close>
and vice versa in goals during a proof.
\<close>

subsubsection "The \<open>subst\<close> Method" 

text \<open>
Rewriting is performed by the method
@{theory_text[display]
\<open>subst name\<close>}
where \<open>name\<close> references an equality fact. The method only affects the first goal. If the
referenced fact has the form \<open>a = b\<close> the method replaces the first occurrence of \<open>a\<close> in
the goal conclusion by \<open>b\<close>. The order of the terms in the equality fact matters, the 
method always substitutes the term on the left by that on the right. 

If the equality contains unknowns unification is used: \<open>a\<close> is
unified with every sub-term of the goal conclusion, the first match is replaced by \<open>b'\<close>
which is \<open>b\<close> after substituting unknowns in the same way as in \<open>a\<close>. If there is no match
of \<open>a\<close> in the goal conclusion an error is signaled.

For a goal \<open>\<lbrakk>A\<^sub>1; \<dots>; A\<^sub>n\<rbrakk> \<Longrightarrow> C\<close> the method only rewrites in the conclusion \<open>C\<close>. The first
match in the assumptions \<open>A\<^sub>1 \<dots> A\<^sub>n\<close> can be substituted by the form
@{theory_text[display]
\<open>subst (asm) name\<close>}
If not only the first match shall be substituted, a number of the match or a range of numbers
may be specified in both forms as in
@{theory_text[display]
\<open>subst (asm) (i..j) name\<close>}

The equality fact can also be a meta equality of the form \<open>a \<equiv> b\<close>. Therefore the method can
be used to expand constant definitions. After the definition
@{theory_text[display]
\<open>definition "inc x \<equiv> x + 1"\<close>}
the method \<^theory_text>\<open>subst inc_def\<close> will rewrite the first occurrence of a function application 
\<open>(inc t)\<close> in the goal conclusion to \<open>(t + 1)\<close>. Remember from Section~\ref{basic-theory-definition}
that the defining equation is automatically named \<open>inc_def\<close>. Note the use of unification to
handle the actual argument term \<open>t\<close>.

The equality fact may be conditional, i.e., it may be a derivation rule with assumptions of the
form \<open>\<lbrakk>RA\<^sub>1; \<dots>; RA\<^sub>m\<rbrakk> \<Longrightarrow> a = b\<close>. When the \<open>subst\<close> method applies a conditional equation of this
form to a goal \<open>\<lbrakk>A\<^sub>1; \<dots>; A\<^sub>n\<rbrakk> \<Longrightarrow> C\<close>, it adds the goals \<open>\<lbrakk>A\<^sub>1; \<dots>; A\<^sub>n\<rbrakk> \<Longrightarrow> RA\<^sub>i'\<close> to the goal state
after rewriting, where \<open>RA\<^sub>i'\<close> result from \<open>RA\<^sub>i\<close> by the unification of \<open>a\<close> in \<open>C\<close>. These
goals are inserted before the original goal, so the next method application will usually process
the goal \<open>\<lbrakk>A\<^sub>1; \<dots>; A\<^sub>n\<rbrakk> \<Longrightarrow> RA\<^sub>1'\<close>.

As an example if there are theorems
@{theory_text[display]
\<open>theorem eq1: "n = 10 \<Longrightarrow> n+3 = 13" for n::nat \<proof>
theorem eq2: "n = 5 \<Longrightarrow> 2*n = 10" for n::nat \<proof>\<close>}
the method \<^theory_text>\<open>subst (2) eq2\<close> replaces the goal \<open>(x::nat) < 5 \<Longrightarrow> 2*x+3 \<le> 2*5 + 3\<close> by the
goals 
@{text[display]
\<open>x < 5 \<Longrightarrow> 5 = 5
x < 5 \<Longrightarrow> 2 * x + 3 \<le> 10 + 3\<close>}
where the first is trivial (but still must be removed by applying a rule). The second 
goal is replaced by the method \<^theory_text>\<open>subst (2) eq1\<close> by
@{text[display]
\<open>x < 5 \<Longrightarrow> 10 = 10
x < 5 \<Longrightarrow> 2 * x + 3 \<le> 13\<close>}

Note that the method \<^theory_text>\<open>subst eq2\<close> would unify \<open>2*n\<close> with the first match \<open>2*x\<close> in the original 
goal and replace it by
@{text[display]
\<open>x < 5 \<Longrightarrow> x = 5
x < 5 \<Longrightarrow> 10 + 3 \<le> 2 * 5 + 3\<close>}
where the first goal cannot be proven because it is invalid.
\<close>

subsubsection "Simplification" 

text\<open>
If the term \<open>b\<close> in an equation \<open>a = b\<close> is in some sense ``simpler'' than \<open>a\<close>, the goal will
also become simpler by successful rewriting with the equation. If there are several
such equations a goal can be replaced by successively simpler goals by rewriting with these
equations. This technique can contribute to the goal's proof and is called ``simplification''.

Basically, simplification uses a set of equations and searches an equation in the set where 
the left hand side unifies with a sub-term in the goal, then substitutes it. This step is 
repeated until no sub-term in the goal unifies with a left hand side in an equation in the set.

It is apparent that great care must be taken when populating the set of equations, otherwise 
simplification may not terminate. If two equations \<open>a = b\<close> and \<open>b = a\<close> are in the set simplification
will exchange matching terms forever. If an equation \<open>a = a+0\<close> is in the set, a term matching
\<open>a\<close> will be replaced by an ever growing sum with zeroes.

Simplification with a set of definitional equations from constant definitions (see 
Section~\ref{basic-theory-definition}) always terminates. Since constant definitions cannot 
be recursive, every substitution removes one occurrence of a defined constant from the goal. 
Simplification terminates if no defined constant from the set remains in the goal.
Although the resulting goal usually is larger than the original goal, it is simpler in the 
sense that it uses fewer defined constants.

If the set contains conditional equations, simplification may produce additional goals. Then 
simplification is applied to these goals as well. Together, simplification may turn a single
complex goal into a large number of simple goals, but it cannot reduce the number of goals.
Therefore simplification is usually complemented by methods which remove trivial goals 
like \<open>x = x\<close>, \<open>A \<Longrightarrow> A\<close>, and \<open>True\<close>. Such an extended simplification may completely solve and remove 
the goal to which it is applied.
\<close>

subsubsection "The \<open>simp\<close> Method"

text\<open>
Isabelle supports simplification by the method
@{theory_text[display]
\<open>simp\<close>}
which is also called ``the simplifier''. It uses the dynamic fact set \<open>simp\<close> as the set of 
equations, which is also called ``the simpset''. The method only affects the first goal. 
If no equation in \<open>simp\<close> is applicable to it or it is not modified by the applicable equations 
an error is signaled.

The \<open>simp\<close> method simplifies the whole goal, i.e., it applies rewriting to the conclusion and 
to all assumptions.

The simpset may contain facts which are not directly equations, but can be converted to an
equation. In particular, an arbitrary derivation rule \<open>\<lbrakk>A\<^sub>1; \<dots>; A\<^sub>n\<rbrakk> \<Longrightarrow> C\<close> can always be
converted to the equation \<open>\<lbrakk>A\<^sub>1; \<dots>; A\<^sub>n\<rbrakk> \<Longrightarrow> C = True\<close>. The simplifier performs this conversion
if no other conversion technique applies, therefore the simpset may actually contain arbitrary 
facts.

The \<open>simp\<close> method also detects several forms of trivial goals and removes them. Thus a complete
proof may be performed by a single application of the simplifier in the form
@{theory_text[display]
\<open>by simp\<close>}

In Isabelle HOL (see Section~\ref{hol}) the simpset is populated with a large number of facts
which make the simplifier a very useful proof tool. Actually all examples of facts used
in the previous sections can be proven by the simplifier:
@{theory_text[display]
\<open>theorem example1: "(x::nat) < c \<Longrightarrow> n*x \<le> n*c" by simp
theorem example2: "(x::nat) \<le> c \<Longrightarrow> x + m \<le> c + m" by simp
theorem "(x::nat) < 5 \<Longrightarrow> 2*x+3 \<le> 2*5 + 3" by simp
theorem eq1: "n = 10 \<Longrightarrow> n+3 = 13" for n::nat by simp
theorem eq2: "n = 5 \<Longrightarrow> 2*n = 10" for n::nat by simp
\<close>}
\<close>

subsubsection "Configuring the Simplifier"

text \<open>
The simplifier can be configured by modifying the equations it uses. The form
@{theory_text[display]
\<open>simp add: name\<^sub>1 \<dots> name\<^sub>n\<close>}
uses the facts \<open>name\<^sub>1, \<dots>, name\<^sub>n\<close> in addition to the facts in the simpset for its rewriting
steps. The form 
@{theory_text[display]
\<open>simp del: name\<^sub>1 \<dots> name\<^sub>n\<close>}
uses only the facts from the simpset without the facts \<open>name\<^sub>1, \<dots>, name\<^sub>n\<close>, and the form
@{theory_text[display]
\<open>simp only: name\<^sub>1 \<dots> name\<^sub>n\<close>}
uses only the facts \<open>name\<^sub>1, \<dots>, name\<^sub>n\<close>. The three forms can be arbitrarily combined.

As usual, a theorem may be added permanently to the simpset as described in 
Section~\ref{basic-theory-theorem} by specifying it as
@{theory_text[display]
\<open>theorem [simp]: "prop" \<proof>\<close>}
and the defining equation of a definition can be added by
@{theory_text[display]
\<open>definition name::type where [simp]: "name \<equiv> term"\<close>}

Adding own constant definitions to the simplifier is a common technique to expand the definition
during simplification. However, this may also have a negative effect: If an equation has been 
specified using the defined constant, it is no more applicable for rewriting after expanding
the definition. Note that the facts in the simpset and the facts provided by \<open>add:\<close>, \<open>del:\<close>, and
\<open>only:\<close> are not simplified themselves, the defined constant will not be expanded there.

Therefore it is usually not recommended to add defining equations to the simpset permanently.
Instead, they can be specified by \<open>add:\<close> when they really shall be expanded during simplification.
\<close>

subsubsection "Splitting Terms"

text \<open>
There are certain terms in which the simplifier will not apply its simpset rules. A typical
example are terms with an internal case distinction (see Section~\ref{hol-terms-case}). To 
process such terms in a goal conclusion the terms must be split. Splitting a term usually results
in several new goals with simpler terms which are then further processed by the simplifier.

Term splitting is done by applying specific rules to the goal. These rules are called ``split
rules''. Usually split rules are not automatically determined and applied by the simplifier, this 
must be configured explicitly in the form
@{theory_text[display]
\<open>simp split: name\<^sub>1 \<dots> name\<^sub>n\<close>}
where the \<open>name\<^sub>i\<close> are the names of the split rules to use. This configuration can be arbitrarily 
combined with the other simplifier configuration options.
\<close>

subsubsection "Input Facts for the \<open>simp\<close> Method"

text \<open>
As usual, facts may be input to the \<open>simp\<close> method. Like the empty method (see 
Section~\ref{basic-methods-empty}) it inserts these facts as assumptions into the goal,
before it starts simplification. Since simplification is also applied to the assumptions,
the input facts will be simplified as well.

As a possible effect of this behavior, after simplifying an input fact and the goal conclusion
the results may unify, leading to the situation where the goal is removed by the \<open>assumption\<close>
method (see Section~\ref{basic-methods-rule}). This is also done by the simplifier, hence in this 
way the input fact may contribute to prove the goal.
\<close>

subsubsection "The \<open>simp_all\<close> Method"

text \<open>
The method
@{theory_text[display]
\<open>simp_all\<close>}
behaves like the \<open>simp\<close> method but processes all goals. It inserts input facts to all goals
in the goal state and simplifies them. If it fails for all goals an error is signaled. Otherwise
it simplifies only the goals for which it does not fail. If it achieves to remove all goals 
the proof is finished.

The \<open>simp_all\<close> method can be configured by \<open>add:\<close>, \<open>del:\<close>, and \<open>only:\<close> in the same way as 
the \<open>simp\<close> method.

The \<open>simp_all\<close> method is useful, if first a method \<open>method\<close> is applied to the goal which splits 
it into several subgoals which all can be solved by simplification. Then the complete
proof can be written as
@{theory_text[display]
\<open>by method simp_all\<close>}
\<close>

subsubsection "Debugging the Simplifier"

text \<open>
If the simplifier fails, it may be difficult to find out the reason. There are several debugging
techniques which may help.

The content of the simpset can be displayed by the command
@{theory_text[display]
\<open>print_simpset\<close>}
which may be written in the proof text in modes \<open>proof(prove)\<close> and \<open>proof(state)\<close> and outside 
of proofs. In the interactive editor the result is displayed in the Output panel (see 
Section~\ref{system-jedit-output}).

There is also a simplifier trace which displays the successful rewrite steps. It is activated
by the command
@{theory_text[display]
\<open>declare [[simp_trace_new depth=n]]\<close>}
outside a theorem or definition. The number \<open>n\<close> should be atleast \<open>2\<close>. When the cursor is
positioned on an application of the \<open>simp\<close> method the button ``Show trace'' can be used
in the Simplifier Trace Panel to display the trace in a separate window. See the documentation
for more information about how to use the trace.

Another technique is to replace the \<open>simp\<close> method by a sequence of \<open>subst\<close> method applications
and explicitly specify the equations which should have been used. To do this for a structured
proof, replace it by a proof script for the  \<open>subst\<close> methods.
\<close>

subsection "Other Automatic Proof Methods"
text_raw\<open>\label{basic-methods-auto}\<close>

text\<open>
Isabelle provides several other proof methods which internally perform several steps,
like the simplifier.
\<close>

subsubsection "Automatic Methods"

text\<open>
The following list contains automatic methods other than \<open>simp\<close>:
\<^item> \<open>blast\<close> mainly applies logical rules and can be used to solve complex logical formulas.
\<^item> \<open>clarify\<close> is similar but does not split goals and does not follow unsafe paths. It can
be used to show the problem if \<open>blast\<close> fails.
\<^item> \<open>auto\<close> combines logical rule application with simplification. It processes all goals and
leaves those it cannot solve.
\<^item> \<open>clarsimp\<close> combines \<open>clarify\<close> with simplification. It processes only the first goal and
usually does not split goals.
\<^item> \<open>fastforce\<close> uses more techniques than \<open>auto\<close>, but processes only the first goal.
\<^item> \<open>force\<close> uses even more techniques and tries to solve the first goal.

The methods which do simplification can be configured like the simplifier by adding 
specifications \<open>simp add:\<close>, \<open>simp del:\<close>, \<open>simp only:\<close>, and \<open>split:\<close>. For example, additional
simplification rules can be specified for the \<open>auto\<close> method in the form
@{theory_text[display]
\<open>auto simp add: name\<^sub>1 \<dots> name\<^sub>n\<close>}

For more information about these methods see the Isabelle documentation.
\<close>

subsubsection "Trying Methods"

text\<open>
Instead of manually trying several automatic methods it is possible to specify the command
@{theory_text[display]
\<open>try\<close>}
anywhere in mode \<open>proof(prove)\<close>, i.e. at the beginning of a proof or in a proof script.
It will try many automatic proof methods and describe the result in the Output window.
It may take some time until results are displayed, in particular, if the goal is invalid and
cannot be proven.

If \<^theory_text>\<open>try\<close> finds a proof for one or more goals it displays them as single proof methods, which, 
by clicking on them can be copied to the cursor position in the text area. The \<^theory_text>\<open>try\<close> command
must be removed manually.

If \<^theory_text>\<open>try\<close> tells you that the goal can be ``directly solved'' by some fact, you can prove it
by the \<open>fact\<close> method, but that also means that there is already a fact of the same form and
your theorem is redundant.

It may also be the case that \<^theory_text>\<open>try\<close> finds a counterexample, meaning that the goal is invalid 
and cannot be proven.
\<close>

section "Case Based Proofs"
text_raw\<open>\label{basic-case}\<close>

text \<open>
If a proof method splits a goal at the beginning of a structured proof the resulting subgoals 
must be proven separately, each with an own \<^theory_text>\<open>show\<close> statement. Some proof methods provide
support for this by initializing a proof context for each goal resulting from the method
application.
\<close>

subsection "Goal Cases"
text_raw\<open>\label{basic-case-goals}\<close>

text \<open>
If a method supports this, it creates a ``case'' for each corresponding goal. The cases are
named. Using these names a proof context can be populated with elements prepared by the method.
\<close>

subsubsection "Named Contexts"

text \<open>
Every case name is associated with proof context elements, thus it can be seen as a named
context which has been prepared by the method for later use. Such named contexts may contain
facts, local variables, and term abbreviations. The actual content depends on the proof method
and the goals for which the cases are created.

When the named context is used in a proof, its content is ``injected'' into the current proof 
context. Usually a named context is used in this way to initialize a new nested context immediately
after its beginning. 
\<close>

subsubsection "The \<^theory_text>\<open>case\<close> Command"

text \<open>
A case may be injected into the current proof context by the command
@{theory_text[display]
\<open>case name\<close>}
where \<open>name\<close> is the case name. It mainly has the effect of the sequence
@{theory_text[display]
\<open>fix x\<^sub>1 \<dots> x\<^sub>k
let ?a\<^sub>1 = t\<^sub>1 and \<dots> ?a\<^sub>m = t\<^sub>m
assume name: "A\<^sub>1" \<dots> "A\<^sub>n"
\<close>}
where \<open>x\<^sub>1 \<dots> x\<^sub>k\<close> are the local variables, \<open>?a\<^sub>1, \<dots>, ?a\<^sub>m\<close> are the term abbreviations, and
\<open>A\<^sub>1, \<dots>, A\<^sub>n\<close> are the facts in the named context of the case. The facts are injected as assumptions
and the set of these assumptions is named using the case name. Moreover, like the \<^theory_text>\<open>assume\<close>
statement the \<^theory_text>\<open>case\<close> command makes the assumed facts current.

Instead of using the case name for naming the assumptions an explicit assumption name \<open>aname\<close> may be 
specified:
@{theory_text[display]
\<open>case aname: name\<close>}

The local variables \<open>x\<^sub>1 \<dots> x\<^sub>k\<close> are fixed by the \<^theory_text>\<open>case\<close> command but are hidden, they cannot be
used in the subsequent proof text. If they should be used, explicit names must be specified for
them in the form
@{theory_text[display]
\<open>case (name y\<^sub>1 \<dots> y\<^sub>j)\<close>}
Then the names \<open>y\<^sub>1 \<dots> y\<^sub>j\<close> can be used to reference the fixed variables in the current proof 
context. If fewer names are specified only the first variables are named, if more names are
specified than there are local variables in the case an error is signaled.

When methods create named contexts they usually only define the term abbreviation \<open>?case\<close> for
the conclusion of the corresponding goal.
\<close>

subsubsection "Proof Structure with Cases"

text \<open>
The usual proof structure using cases consists of a sequence of nested contexts. At its 
beginning each context is initialized by a \<^theory_text>\<open>case\<close> command, at its end it uses a \<^theory_text>\<open>show\<close> 
statement to remove the corresponding goal:
@{theory_text[display]
\<open>proof `method`
case name\<^sub>1
\<dots>
show ?case \<proof>
next
case name\<^sub>2
\<dots>
show ?case \<proof>
next
\<dots>
next
case name\<^sub>n
\<dots>
show ?case \<proof>
qed
\<close>}
Every \<^theory_text>\<open>show\<close> command uses the local term abbreviation \<open>?case\<close> to refer to the conclusion of
the corresponding goal.

In the interactive editor, when the cursor is positioned on \<^theory_text>\<open>proof `method`\<close> where the method
supports cases, a skeleton of such a proof using the specific cases provided by the method is 
displayed in the Output panel. By clicking on it 
it may be copied into the text area immediately after the method specification.
\<close>

subsection \<open>The {\sl goal$\_$cases} Method\<close>
text_raw\<open>\label{basic-case-goalcases}\<close>

text\<open>
The simplest method with support for cases is
@{theory_text[display]
\<open>goal_cases\<close>}
Without modifying the goal state it creates a named case for every existing goal. Input facts
are ignored.

For a goal \<^theory_text>\<open>\<And> x\<^sub>1 \<dots> x\<^sub>m. \<lbrakk>A\<^sub>1; \<dots>; A\<^sub>n\<rbrakk> \<Longrightarrow> C\<close> the created named context contains the local variables
\<open>x\<^sub>1 \<dots> x\<^sub>m\<close>, the facts \<open>A\<^sub>1, \<dots>, A\<^sub>n\<close>, and the term abbreviation \<open>?case\<close> bound to \<open>C\<close>. If the goal
contains variables which are not explicitly bound by \<open>\<And>\<close> these variables are not added to the
context.

The effect is that if no other variables are fixed and no other facts are assumed a statement
\<^theory_text>\<open>show ?case\<close> after the corresponding \<^theory_text>\<open>case\<close> command will match the goal.

The cases are named by numbers starting with \<open>1\<close>. If other names should be used they can be specified
as arguments to the method:
@{theory_text[display]
\<open>goal_cases name\<^sub>1 \<dots> name\<^sub>n\<close>}
If fewer names are specified than goals are present, only for the first \<open>n\<close> goals cases are created.
If more names are specified an error is signaled.

When \<^theory_text>\<open>goal_cases\<close> is used in a composed proof method it can provide cases for the goals produced
by arbitrary other methods:
@{theory_text[display]
\<open>proof (method, goal_cases)\<close>}
provides cases for all goals existing after \<^theory_text>\<open>method\<close> has been applied. If \<^theory_text>\<open>method\<close> does not split
the goal there will be only one case. This can be useful to work with a goal produced by 
\<^theory_text>\<open>method\<close>. In particular, the conclusion of that goal is available as \<open>?case\<close>.

Note that the proof state(s) resulting from \<^theory_text>\<open>goal_cases\<close> are not visible for the reader of the proof.
Therefore it should only be applied if the goals produced by \<^theory_text>\<open>method\<close> are apparent.
This can be supported by defining an abbreviated form of the conclusion by 
@{theory_text[display]
\<open>let "pattern" = ?case\<close>}
\<close>

subsection "Case Based Reasoning"
text_raw\<open>\label{basic-case-reasoning}\<close>

text\<open>
In ``case based reasoning'' a goal is proven by processing ``all possible cases'' for an additional
assumption separately. If the conclusion can be proven for all these cases and the cases cover all
possibilities, the conclusion holds generally.

In the simplest form a single proposition is used as additional assumption. Then there are only two 
cases: if the proposition is \<open>True\<close> or if it is \<open>False\<close>.

Consider the derivation rule \<open>(x::nat) < c \<Longrightarrow> n*x \<le> n*c\<close> from Section~\ref{basic-theory-prop}. As
additional assumption the proposition whether \<open>n\<close> is zero can be used. Then there are the two cases 
\<open>n = 0\<close> and \<open>n \<noteq> 0\<close> and clearly these cover all possibilities. Using the first case as assumption 
implies that \<open>n*x\<close> and \<open>n*c\<close> are both zero and thus \<open>n*x = n*c\<close>. Using the second case as assumption
together with the original assumption implies that \<open>n*x < n*c\<close>. Together the conclusion \<open>n*x \<le> n*c\<close>
follows.
\<close>

subsubsection "Case Rules"

text\<open>
To prove a goal in this way it must be split into a separate goal for each case. All these goals
must have the same conclusion but differ in the additional assumptions. This splitting can be done
by applying a meta-rule of the form
@{text[display]
\<open>\<lbrakk>Q\<^sub>1 \<Longrightarrow> ?P; ...; Q\<^sub>n \<Longrightarrow> ?P\<rbrakk> \<Longrightarrow> ?P\<close>}
Such rules are called ``case rules''.

When this case rule is applied to a goal \<^theory_text>\<open>\<And> x\<^sub>1 \<dots> x\<^sub>m. \<lbrakk>A\<^sub>1; \<dots>; A\<^sub>n\<rbrakk> \<Longrightarrow> C\<close> as described in 
Section~\ref{basic-methods-rule}, it unifies \<open>?P\<close> with the conclusion \<open>C\<close> and replaces the goal
by the \<open>n\<close> goals
@{text[display]
\<open>\<And> x\<^sub>1 \<dots> x\<^sub>m. \<lbrakk>A\<^sub>1; \<dots>; A\<^sub>n; Q\<^sub>1\<rbrakk> \<Longrightarrow> C
\<dots>
\<And> x\<^sub>1 \<dots> x\<^sub>m. \<lbrakk>A\<^sub>1; \<dots>; A\<^sub>n; Q\<^sub>n\<rbrakk> \<Longrightarrow> C\<close>}
where every goal has one of the propositions \<open>Q\<^sub>i\<close> as additional assumption.

The case rule is only valid, if the \<open>Q\<^sub>i\<close> together cover all possibilities, i.e., if 
\<open>Q\<^sub>1 \<or> \<dots> \<or> Q\<^sub>n\<close> holds. Then it has been proven and is available as a fact which can be applied.
Since the whole conclusion is the single unknown \<open>?P\<close> it unifies with every proposition used as
conclusion in a goal, hence a case rule can always be applied to arbitrary goals. It 
depends on the \<open>Q\<^sub>i\<close> whether splitting a specific goal with the case rule is useful for proving
the goal.

A case rule for testing a natural number for being zero would be
@{text[display]
\<open>\<lbrakk>?n = 0 \<Longrightarrow> ?P; ?n \<noteq> 0 \<Longrightarrow> ?P\<rbrakk> \<Longrightarrow> ?P\<close>}
It contains the number to be tested as the unknown \<open>?n\<close>, so that an arbitrary term can be substituted
for it. This is not automatically done by unifying \<open>?P\<close> with the goal's conclusion, thus the rule 
must be ``prepared'' for 
application to a specific goal. To apply it to the goal \<open>(x::nat) < c \<Longrightarrow> n*x \<le> n*c\<close> in the intended
way the unknown \<open>?n\<close> must be substituted by the variable \<open>n\<close> from the goal conclusion. If the 
prepared rule is then applied to the goal it splits it into the goals
@{text[display]
\<open>\<lbrakk>(x::nat) < c; n = 0\<rbrakk> \<Longrightarrow> n*x \<le> n*c
\<lbrakk>(x::nat) < c; n \<noteq> 0\<rbrakk> \<Longrightarrow> n*x \<le> n*c\<close>}
which can now be proven separately.

Actually, the much more general case rule 
@{text[display]
\<open>\<lbrakk>?Q \<Longrightarrow> ?P; \<not> ?Q \<Longrightarrow> ?P\<rbrakk> \<Longrightarrow> ?P\<close>}
is used for this purpose. Here the unknown \<open>?Q\<close> represents the complete proposition to be used as
additional assumption, therefore the rule can be used for arbitrary propositions. By substituting 
the term \<open>n = 0\<close> for \<open>?Q\<close> the rule is prepared to be applied in the same way as above.

Case rules may even be more general than shown above. Instead of a single proposition \<open>Q\<^sub>i\<close> every 
case may have locally bound variables and an arbitrary number of assumptions, resulting in the
most general form
@{text[display]
\<open>\<lbrakk>\<And>x\<^sub>1\<^sub>1\<dots>x\<^sub>1\<^sub>k\<^sub>1. \<lbrakk>Q\<^sub>1\<^sub>1;\<dots>;Q\<^sub>1\<^sub>m\<^sub>1\<rbrakk> \<Longrightarrow> ?P;
  \<dots>;
 \<And>x\<^sub>n\<^sub>1\<dots>x\<^sub>n\<^sub>k\<^sub>n. \<lbrakk>Q\<^sub>n\<^sub>1;\<dots>;Q\<^sub>n\<^sub>m\<^sub>n\<rbrakk> \<Longrightarrow> ?P\<rbrakk> \<Longrightarrow> ?P\<close>}
of a case rule. When applied it splits the goal and adds the variables \<open>x\<^sub>i\<^sub>1 \<dots> x\<^sub>i\<^sub>k\<^sub>i\<close> and the assumptions
\<open>Q\<^sub>i\<^sub>1 \<dots> Q\<^sub>i\<^sub>m\<^sub>i\<close> to the \<open>i\<close>th case.
\<close>

subsubsection "The \<^theory_text>\<open>cases\<close> Method"

text\<open>
Case based reasoning can be performed in a structured proof using the method \<^theory_text>\<open>cases\<close> in the form
@{theory_text[display]
\<open>cases "term" rule: name\<close>}
where \<open>name\<close> is the name of a valid case rule. The method prepares the rule by substituting the
specified \<open>term\<close> for the unknown in the assumptions, and applies the rule to the first goal in the
goal state. 

Additionally, the method creates a named context for every goal resulting from the rule
application. The context contains the variables and assumptions specified in the corresponding
case in the case rule. For the most general form depicted above the context for the \<open>i\<close>th case 
contains the variables \<open>x\<^sub>i\<^sub>1 \<dots> x\<^sub>i\<^sub>k\<^sub>i\<close> and the assumptions \<open>Q\<^sub>i\<^sub>1 \<dots> Q\<^sub>i\<^sub>m\<^sub>i\<close>. No term abbreviation
\<open>?case\<close> is defined, because the conclusion of every new goal is the same as that of the original 
goal, thus the existing abbreviation \<open>?thesis\<close> can be used instead.

Often a case rule has only one unknown in the case assumptions. If there are more, several terms
may be specified in the \<^theory_text>\<open>cases\<close> method for preparing the rule.

The \<^theory_text>\<open>cases\<close> method treats input facts like the empty method (see Section~\ref{basic-methods-empty}) by 
inserting them as assumptions into the original goal before splitting it.
 
Like the \<^theory_text>\<open>rule\<close> method (see Section~\ref{basic-methods-rule}) the \<^theory_text>\<open>cases\<close> method supports
automatic rule selection for the case rule and may be specified in the form
@{theory_text[display]
\<open>cases "term"\<close>}
Normally the rule is selected according to the type of the specified \<open>term\<close>. In Isabelle HOL (see 
Section~\ref{hol}) most types have an associated case rule. 

The rule \<open>\<lbrakk>?Q \<Longrightarrow> ?P; \<not> ?Q \<Longrightarrow> ?P\<rbrakk> \<Longrightarrow> ?P\<close>
depicted above is associated with type \<open>bool\<close>. Therefore the case splitting for comparing \<open>n\<close> with
zero can be done by the method
@{theory_text[display]
\<open>cases "n = 0"\<close>}

The names used for the contexts created by the \<^theory_text>\<open>cases\<close> method can be specified by attributing the case rule.
The case rule for \<open>bool\<close> is attributed to use the case names \<open>True\<close> and \<open>False\<close>. Note that these are 
names, not the constants for the values of type \<open>bool\<close>. 

The proof writer may not know the case names specified by the automatically selected case rule.
However, they can be determined from the proof skeleton which is displayed in the interactive editor
when the cursor is positioned on the \<^theory_text>\<open>cases\<close> method (see Section~\ref{basic-case-goals}).

Together, a structured proof for the goal
\<open>(x::nat) < c \<Longrightarrow> n*x \<le> n*c\<close> with case splitting may have the form
@{theory_text[display]
\<open>proof (cases "n = 0")
case True
\<dots>
show ?thesis \<proof>
next
case False
\<dots>
show ?thesis \<proof>
qed\<close>}
The \<^theory_text>\<open>cases\<close> method adds the assumptions \<open>n=0\<close> and \<open>n\<noteq>0\<close> to the goals of the cases, the \<^theory_text>\<open>case\<close> 
commands add them as assumed facts to the local context, so that they are part of the rule exported
by the \<^theory_text>\<open>show\<close> statement and match the assumption in the corresponding goal.

Note that the \<^theory_text>\<open>case\<close> command adds only the assumptions originating from the case rule. The other
assumptions in the original goal (here \<open>x < c\<close>) must be added to the context in the usual ways (see 
Section~\ref{basic-proof-assume}) if needed for the proof.
\<close>

subsection "Induction"

text\<open>
With induction a goal is proven by processing ``all possible cases'' for certain values which
occur in it. If the goal can be proven for all these cases and the cases cover all
possibilities, the goal holds generally. A specific
technique is to assume the goal for some values and then prove it for other values. In this
way it is possible to cover infinite value sets by proofs for only a finite number of values and 
steps from values to other values.

The best known example of induction is a proposition which is proven for the natural number \<open>0\<close> and
the step from a number \<open>n\<close> to its successor \<open>n+1\<close>, which covers the whole infinite set of natural
numbers. 

As a (trivial) example consider the proposition \<open>0\<le>n\<close>. To prove that it is valid for all natural numbers
\<open>n\<close> we prove the ``base case'' where \<open>n\<close> is \<open>0\<close>, which is true because \<open>0\<le>0\<close>. Then we prove the
``induction step'', by assuming that \<open>0\<le>n\<close> (the ``induction hypothesis'') and proving that \<open>0\<le>n+1\<close> 
follows, which is true because addition increases the value.
\<close>

subsubsection "Induction Rules"

text\<open>
Like for case based reasoning (see Section~\ref{basic-case-reasoning}) a goal is split into these
cases by applying a meta-rule. For induction these rules are called ``induction rules'' and have
the general form
@{text[display]
\<open>\<lbrakk>P\<^sub>1 ; ...; P\<^sub>n \<rbrakk> \<Longrightarrow> ?P ?a\<^sub>1 \<dots> ?a\<^sub>m\<close>}
where every \<open>P\<^sub>i\<close> is a rule of the form
@{text[display]
\<open>\<And>y\<^sub>i\<^sub>1 \<dots> y\<^sub>i\<^sub>p\<^sub>i. \<lbrakk>Q\<^sub>i\<^sub>1; \<dots>; Q\<^sub>i\<^sub>q\<^sub>i\<rbrakk> \<Longrightarrow> ?P term\<^sub>i\<^sub>1 \<dots> term\<^sub>i\<^sub>m\<close>}
where the assumptions \<open>Q\<^sub>i\<^sub>j\<close> may contain the unknown \<open>?P\<close> but no other unknowns, in particular none
of the \<open>?a\<^sub>1 \<dots> ?a\<^sub>m\<close>. A rule for a base case usually has no bound variables \<open>y\<^sub>i\<^sub>j\<close> and no assumptions
\<open>Q\<^sub>i\<^sub>j\<close>, at least the \<open>Q\<^sub>i\<^sub>j\<close> do not contain \<open>?P\<close>. 

Note that the \<open>?a\<^sub>1 \<dots> ?a\<^sub>m\<close> only occur once in the conclusion of the meta-rule and nowhere else. Like
the case rules induction rules must be ``prepared'' for use, this is done by replacing the \<open>?a\<^sub>1 \<dots> ?a\<^sub>m\<close>
by specific terms \<open>term\<^sub>1 \<dots> term\<^sub>m\<close>. These are the terms for which all possible cases shall be processed
in the goal.

When a prepared induction rule is applied to a goal \<open>\<And> x\<^sub>1 \<dots> x\<^sub>m. \<lbrakk>A\<^sub>1; \<dots>; A\<^sub>n\<rbrakk> \<Longrightarrow> C\<close> as described in 
Section~\ref{basic-methods-rule}, it unifies \<open>?P term\<^sub>1 \<dots> term\<^sub>m\<close> with the conclusion \<open>C\<close>. This has
the effect of abstracting \<open>C\<close> to a (boolean) function \<open>PC\<close> by identifying all places where the \<open>term\<^sub>i\<close>
occur in \<open>C\<close> and replacing them by the function arguments. The function \<open>PC\<close> is then bound to the 
unknown \<open>?P\<close>, so that applying \<open>?P\<close> to the arguments \<open>term\<^sub>1 \<dots> term\<^sub>m\<close> again yields \<open>C\<close>. The function
\<open>PC\<close> is the property to be proven for all argument values. Therefore the cases of the proof
can be described by applying \<open>?P\<close> to terms for the specific values in the rules \<open>P\<^sub>i\<close> for the cases. 
The rule application results in the \<open>n\<close> goals
@{text[display]
\<open>\<And> x\<^sub>1 \<dots> x\<^sub>m y\<^sub>1\<^sub>1 \<dots> y\<^sub>1\<^sub>p\<^sub>1. \<lbrakk>A\<^sub>1; \<dots>; A\<^sub>n; Q\<^sub>1\<^sub>1; \<dots>; Q\<^sub>1\<^sub>q\<^sub>1\<rbrakk> \<Longrightarrow> PC term\<^sub>1\<^sub>1 \<dots> term\<^sub>1\<^sub>m
\<dots>
\<And> x\<^sub>1 \<dots> x\<^sub>m y\<^sub>n\<^sub>1 \<dots> y\<^sub>n\<^sub>p\<^sub>n. \<lbrakk>A\<^sub>1; \<dots>; A\<^sub>n; Q\<^sub>n\<^sub>1; \<dots>; Q\<^sub>n\<^sub>q\<^sub>n\<rbrakk> \<Longrightarrow> PC term\<^sub>n\<^sub>1 \<dots> term\<^sub>n\<^sub>m\<close>}
If some of the \<open>y\<^sub>i\<^sub>j\<close> collide with some of the \<open>x\<^sub>i\<close> they are consistently renamed.

The induction rule is only valid if for every argument position \<open>j\<close> of \<open>?P\<close> the terms \<open>term\<^sub>i\<^sub>j\<close>
cover all possible values. Then the induction rule has been proven and is available as a fact which 
can be applied. After preparing the induction rule for application, its conclusion \<open>?P term\<^sub>1 \<dots> term\<^sub>m\<close> 
matches all propositions which contain the terms \<open>term\<^sub>1 \<dots> term\<^sub>m\<close> in one or more copies. It depends 
on the \<open>P\<^sub>i\<close> in the rule whether splitting a specific goal with the induction rule is useful for 
proving the goal.

An induction rule for the natural numbers is
@{text[display]
\<open>\<lbrakk>?P 0; \<And>y. ?P y \<Longrightarrow> ?P (y+1)\<rbrakk> \<Longrightarrow> ?P ?a\<close>}
To apply it to the goal \<open>0\<le>n\<close>, it must be prepared by substituting the variable \<open>n\<close> for the 
unknown \<open>?a\<close>. Then the rule conclusion \<open>?P n\<close> is unified with the goal which abstracts the
goal to the boolean function \<open>PC = (\<lambda>i. 0\<le>i)\<close> and substitutes it for all occurrences of \<open>?P\<close>. 
This results in the rule instance 
\<open>\<lbrakk>(\<lambda>i. 0\<le>i) 0; \<And>y. (\<lambda>i. 0\<le>i) y \<Longrightarrow> (\<lambda>i. 0\<le>i) (y+1)\<rbrakk> \<Longrightarrow> (\<lambda>i. 0\<le>i) n\<close>.
By substituting the arguments in the function applications its assumption part yields the two goals
@{text[display]
\<open>0\<le>0
\<And>y. 0\<le>y \<Longrightarrow> 0\<le>(y+1)\<close>}
which correspond to the base case and induction step as described above.
\<close>

subsubsection "The \<^theory_text>\<open>induction\<close> Method"

text\<open>
Induction can be performed in a structured proof using the method \<^theory_text>\<open>induction\<close> in the form
@{theory_text[display]
\<open>induction "term\<^sub>1" \<dots> "term\<^sub>m" rule: name\<close>}
where \<open>name\<close> is the name of a valid induction rule. The method prepares the rule by substituting the
specified \<open>term\<^sub>i\<close> for the unknowns \<open>?a\<^sub>1 \<dots> ?a\<^sub>m\<close> and applies the rule to the first goal in the
goal state. 

Additionally, the method creates a named context for every goal resulting from the rule
application. The context contains the variables and assumptions specified in the corresponding
case in the induction rule. For the most general form depicted above the context for the \<open>i\<close>th case 
contains the variables \<open>x\<^sub>1 \<dots> x\<^sub>m y\<^sub>i\<^sub>1 \<dots> y\<^sub>i\<^sub>p\<^sub>i\<close> and the assumptions \<open>A\<^sub>1; \<dots>; A\<^sub>n; Q\<^sub>i\<^sub>1; \<dots>; Q\<^sub>i\<^sub>q\<^sub>i\<close>. 
The term abbreviation \<open>?case\<close> is defined for the case conclusion \<open>PC term\<^sub>1\<^sub>1 \<dots> term\<^sub>1\<^sub>m\<close> which is to
be proven for the case.

The \<^theory_text>\<open>induction\<close> method treats input facts like the empty method (see Section~\ref{basic-methods-empty})
and the \<^theory_text>\<open>cases\<close> method (see Section~\ref{basic-case-reasoning}) by inserting them as assumptions 
into the original goal before splitting it.

Also like the \<^theory_text>\<open>cases\<close> method the \<^theory_text>\<open>induction\<close> method supports
automatic rule selection for the induction rule. This is only possible if only one term is specified
in the method:
@{theory_text[display]
\<open>induction "term"\<close>}
Then the rule is selected according to the type of the specified \<open>term\<close>. In Isabelle HOL (see 
Section~\ref{hol}) most types have an associated induction rule. 

The rule \<open>\<lbrakk>?P True; ?P False\<rbrakk> \<Longrightarrow> ?P ?a\<close> is associated with type \<open>bool\<close>. Therefore induction can be 
applied to every proposition which contains a term of type \<open>bool\<close>, such as the goal \<open>b \<and> False = False\<close>.
Applying the method
@{theory_text[display]
\<open>induct b\<close>}
will split the it into the goals
@{text[display]
\<open>False \<and> False = False
True \<and> False = False\<close>}
which cover all possible cases for \<open>b\<close>. Here, the type has only two values, therefore induction is 
not really needed.

Like for the \<^theory_text>\<open>cases\<close> method (see Section~\ref{basic-case-reasoning}) the names used for the contexts 
created by the \<^theory_text>\<open>induction\<close> method can be specified by attributing the induction rule. They can be 
determined from the proof skeleton which is displayed in the interactive editor
when the cursor is positioned on the \<^theory_text>\<open>induction\<close> method (see Section~\ref{basic-case-goals}).

If the induction rule \<open>\<lbrakk>?P 0; \<And>y. ?P y \<Longrightarrow> ?P (y+1)\<rbrakk> \<Longrightarrow> ?P ?a\<close> for the natural numbers has been
proven and named \<open>induct_nat\<close> with case names \<open>Start\<close> and \<open>Step\<close>, a structured proof for the goal 
\<open>0\<le>n\<close> may have the form
@{theory_text[display]
\<open>proof (induction n rule: induct_nat)
case Start
\<dots>
show ?case \<proof>
next
case Step
\<dots>
show ?case \<proof>
qed\<close>}
The \<^theory_text>\<open>induction\<close> method creates the named contexts \<open>Start\<close> and \<open>Step\<close>. The former has no local 
variables and assumptions and binds \<open>?case\<close> to the proposition \<open>0\<le>0\<close>, the latter has the local
variable \<open>y\<close>, the assumption \<open>0\<le>y\<close> named \<open>Step\<close> and binds \<open>?case\<close> to the proposition \<open>0 \<le> y + 1\<close>.

If the rule \<open>induct_nat\<close> has been associated with type \<open>nat\<close> the rule specification
may be omitted in the method:
@{theory_text[display]
\<open>proof (induction n)
\<dots>
\<close>}
\<close>

subsubsection "Assumptions"

text\<open>
Some care must be taken to apply induction rules correctly.

As described above, the prepared rule's conclusion \<open>?P term\<^sub>1 \<dots> term\<^sub>m\<close> is only unified with the 
conclusion \<open>C\<close> of the goal to determine the function \<open>PC\<close> which is substituted for \<open>?P\<close> in the
induction rule. The assumptions \<open>A\<^sub>1 \<dots> A\<^sub>n\<close> in the goal are completely ignored, although they are
included in the goals after splitting. If the assumptions share free variables with the conclusion
\<open>C\<close> this connection is broken after applying the prepared induction rule. 

Consider the goal
@{text[display]
\<open>4 < n \<Longrightarrow> 5 \<le> n\<close>}
When applying the prepared induction rule for the natural numbers
\<open>\<lbrakk>?P 0; \<And>y. ?P y \<Longrightarrow> ?P (y+1)\<rbrakk> \<Longrightarrow> ?P n\<close> the conclusions will be matched which leads to the 
abstracted function \<open>(\<lambda>i. 5\<le>i)\<close> and the resulting goals are
@{text[display]
\<open>4 < n \<Longrightarrow> 5 \<le> 0
\<And>y. \<lbrakk>4 < n; 5 \<le> y\<rbrakk> \<Longrightarrow> 5 \<le> (y+1)\<close>}
where the first goal is invalid. Although the second goal is valid, it shows that the relation
between the variable \<open>n\<close> in the assumption and the variable \<open>y\<close> used in the induction rule has been
lost. 
\<close>

subsubsection "Subterms"

text\<open>
**todo**
\<close>

subsubsection "The \<^theory_text>\<open>induct\<close> Method"

text\<open>
**todo**
\<close>
(*
lemma myInduct: "\<lbrakk>P 0; \<And>y. P y \<Longrightarrow> P (y+1)\<rbrakk> \<Longrightarrow> P a" for a::nat
  by (metis add.commute add_cancel_left_left discrete infinite_descent0 le_iff_add less_add_same_cancel2 less_numeral_extra(1))

lemma "4 < n \<Longrightarrow> 5 \<le> n" for n::nat
  apply(induct rule: myInduct)
  apply(rule myInduct[where a=n]) 
  oops

lemma "0\<le>n" for n::nat
proof (induction n rule:myInduct)
  case 1
  then show ?case sorry
next
  case (2 y)
  then show ?case sorry
qed
inductive ev :: "nat \<Rightarrow> bool" where
ev0:
 "ev 0" |
evSS : "ev n \<Longrightarrow> ev (n + 2)"
thm ev.induct

fun evn :: "nat \<Rightarrow> bool" where
"evn 0 = True" |
"evn (Suc 0) = False" |
"evn (Suc(Suc n)) = evn n"
thm evn.induct
thm nat.induct int_of_nat_induct
lemma "ev m \<Longrightarrow> evn m"
apply(induction m rule: ev.induct )
  by(simp_all)

lemma "evn n \<Longrightarrow> ev n"
  apply(rule evn.induct ) sorry

lemma "w = of_nat n + of_nat m" for n::nat and w::int
  apply(induction n m rule: nat.induct) sorry

*)

end
