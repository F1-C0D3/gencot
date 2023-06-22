theory Chapter_holbasic
  imports Chapter_basic
begin

chapter "Isabelle HOL Basics"
text_raw\<open>\label{holbasic}\<close>

text \<open>
The basic mechanisms described in Chapter~\ref{basic} can be used for working with different 
``object logics''. An object logic defines the types of objects available, constants of these types,
and facts about them. An object logic may also extend the syntax, both inner and outer syntax.

The standard object logic for Isabelle is the ``Higher Order Logic'' HOL, it covers a large part
of standards mathematics and is flexibly extensible. This chapter introduces some basic mechanisms
defined by HOL which are used to populate HOL with many of its mathematical objects and functions
and which can also be used to extend HOL to additional kinds of objects. Basically these mechanisms
support the definition of new types.

HOL extends the basic type introduction mechanisms of Isabelle (see Section~\ref{basic-theory-types})
by several ways of specifying the set of values of a new type. This section introduces four of
them: algebraic types, records, subtypes, and quotient types. Additionally it introduces 
some type independent mechanisms which can be used in HOL for arbitrary types.
\<close>

section "Algebraic Types"
text_raw\<open>\label{holbasic-data}\<close>

text\<open>
Roughly an algebraic type is equivalent to a union of cartesian products with support for
recursion. In this way most data types used in programming languages can be covered, such as records,
unions, enumerations, and pointer structures. Therefore Isabelle also uses the notion ``datatype'' 
for algebraic types.
\<close>

subsection "Definition of Algebraic Types"
text_raw\<open>\label{holbasic-data-def}\<close>

text\<open>
Basically, an algebraic type is defined in the form
@{theory_text[display]
\<open>datatype name = alt\<^sub>1 | \<dots> | alt\<^sub>n\<close>}
where \<open>name\<close> is the name of the new algebraic type and every alternative \<open>alt\<^sub>i\<close> is a ``constructor
specification'' of the form
@{theory_text[display]
\<open>cname\<^sub>i "type\<^sub>i\<^sub>1" \<dots> "type\<^sub>i\<^sub>k\<^sub>i"\<close>}
The \<open>cname\<^sub>i\<close> are names and the \<open>type\<^sub>i\<^sub>j\<close> are types.
The types are specified in inner syntax and must be quoted, if they are not a single type name. All 
other parts belong to the outer syntax. 

Recursion is supported for the types, i.e., the name \<open>name\<close> of the defined type may occur in the 
type specifications \<open>type\<^sub>i\<^sub>j\<close>. However, there must be atleast one constructor specification which
is not recursive, otherwise the definition does not ``terminate''. Isabelle checks this condition
and signals an error if it is not satisfied.

As a convention, capitalized names are used in Isabelle HOL for the \<open>cname\<^sub>i\<close>.

An example for a datatype definition with two constructor specifications is
@{theory_text[display]
\<open>datatype coord = 
  Dim2 nat nat
| Dim3 nat nat nat\<close>}
Its value set is equivalent to the union of pairs and triples of natural numbers.

An example for a recursive datatype definition with two constructor specifications is
@{theory_text[display]
\<open>datatype tree = 
  Leaf nat
| Tree nat tree tree\<close>}
Its value set is equivalent to the set of all binary trees with a natural number in every node.
\<close>

subsection "Constructors"
text_raw\<open>\label{holbasic-data-constr}\<close>

text\<open>
Every \<open>cname\<^sub>i\<close> is used by the definition to introduce a ``(value) constructor function'',
i.e., a constant
@{text[display]
\<open>cname\<^sub>i :: "type\<^sub>i\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> type\<^sub>i\<^sub>k\<^sub>i \<Rightarrow> name"\<close>}
which is a function with \<open>ki\<close> arguments mapping their arguments to values of the new type \<open>name\<close>.

Every datatype definition constitutes a separate namespace for the functions it introduces. Therefore
the same names may be used in constructor specifications of different datatype definitions. If used
directly, a name refers to the constructor function of the nearest preceding datatype definition.
To refer to constructor functions with the same name of other datatypes the name may be qualified
by prefixing it with the type name in the form \<open>name.cname\<^sub>i\<close>.

The definition of type \<open>coord\<close> above introduces the two constructor functions \<open>Dim2 :: nat \<Rightarrow> nat \<Rightarrow> coord\<close>
and \<open>Dim3 :: nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> coord\<close>. Their qualified names are \<open>coord.Dim2\<close> and \<open>coord.Dim3\<close>.
\<close>

subsubsection "Constructing Values"

text\<open>
These constructor functions are assumed to be injective, thus their result values differ if atleast
one argument value differs. This implies that the set of all values of the constructor function
\<open>cname\<^sub>i\<close> is equivalent to the cartesian product of the value sets of \<open>type\<^sub>i\<^sub>1 \<dots> type\<^sub>i\<^sub>k\<^sub>i\<close>: for every
tuple of arguments there is a constructed value and vice versa. Note, however, that as usual the
values of the new type are distinct from the values of all other types, in particular, they are
distinct from the argument tuples.

Moreover the result values of different constructor functions are also assumed to be different.
Together the set of all values of the defined type is equivalent to the (disjoint) union of the
cartesian products of all constructor argument types. Moreover, every value of the type may be 
denoted by a term
@{text[display]
\<open>cname\<^sub>i term\<^sub>1 \<dots> term\<^sub>k\<^sub>i\<close>}
where each \<open>term\<^sub>j\<close> is of type  \<open>type\<^sub>i\<^sub>j\<close> and specifies an argument for the constructor function
application.

Values of type \<open>coord\<close> as defined above are denoted by terms such as \<open>Dim2 0 1\<close> and \<open>Dim3 10 5 21\<close>.
\<close>

subsubsection "Constant Constructors and Enumeration Types"

text\<open>
A constructor specification may consist of a single constructor name \<open>cname\<^sub>i\<close>, then the constructor 
functions has no arguments and always constructs the same single value. The constructor is equivalent 
to a constant of type \<open>name\<close>. As a consequence an ``enumeration type'' can be defined in the form
@{theory_text[display]
\<open>datatype three = Zero | One | Two\<close>}
This type \<open>three\<close> has three values denoted by \<open>Zero\<close>, \<open>One\<close>, and \<open>Two\<close>.
\<close>

subsubsection "Types with a Single Constructor"

text\<open>
If a datatype definition consists of a single constructor specification its value set is equivalent 
to the corresponding cartesian product. The corresponding tuples have a separate component for every
constructor argument type. As a consequence a ``record type'' can be defined in the form 
@{theory_text[display]
\<open>datatype recrd = MkRecrd nat "nat set" bool\<close>}
Its values are equivalent to triples where the first component is a natural number, the second
component is a set of natural numbers, and the third component is a boolean value. An example value
is denoted by \<open>MkRecrd 5 {1,2,3} True\<close>.

Since there must be atleast one nonrecursive constructor specification, definitions with a single
constructor specification cannot be recursive.
\<close>

subsection "Destructors"
text_raw\<open>\label{holbasic-data-destr}\<close>

text\<open>
Since constructor functions are injective it is possible to determine for every value of the defined
type the value of each constructor argument used to construct it. Corresponding mechanisms are 
called ``destructors'', there are three different types of them.
\<close>

subsubsection "Selectors"

text\<open>
The most immediate form of a destructor is a selector function. For the constructor argument specified
by \<open>type\<^sub>i\<^sub>j\<close> the selector function is a function of type \<open>name \<Rightarrow> type\<^sub>i\<^sub>j\<close>. For every value constructed
by \<open>cname\<^sub>i term\<^sub>1 \<dots> term\<^sub>k\<^sub>i\<close> it returns the value denoted by \<open>term\<^sub>j\<close>.

The names of selector functions must be specified explicitly. This is done using the extended form
of a constructor specification
@{theory_text[display]
\<open>cname\<^sub>i (sname\<^sub>i\<^sub>1 : "type\<^sub>i\<^sub>1") \<dots> (sname\<^sub>i\<^sub>k\<^sub>i : "type\<^sub>i\<^sub>k\<^sub>i")\<close>}
where the \<open>sname\<^sub>i\<^sub>j\<close> are the names used for the corresponding selector functions. Selector names
may be specified for all or only for some constructor arguments. As for constructors, selector names
belong to the namespace of the defined type and may be qualified by prefixing the type name.

An example datatype definition with selectors is
@{theory_text[display]
\<open>datatype recrd = MkRecrd (n:nat) (s:"nat set") (b:bool)\<close>}
It shows that the selector functions correspond to the field names used in programming languages 
in record types to access the components. For every term \<open>r\<close> of type \<open>recrd\<close> the selector term
\<open>s r\<close> denotes the set component of \<open>r\<close>.

An example for a datatype with multiple constructor specifications is
@{theory_text[display]
\<open>datatype coord = 
  Dim2 (x:nat) (y:nat)
| Dim3 (x:nat) (y:nat) (z:nat)\<close>}
Note that the selectors \<open>x\<close> and \<open>y\<close> are specified in both alternatives. Therefore a single selector
function \<open>x :: coord \<Rightarrow> nat\<close> is defined which yields the first component both for a two-dimensional
and a three-dimensional coordinate and analogously for \<open>y\<close>. If instead the definition is specified as
@{theory_text[display]
\<open>datatype coord = 
  Dim2 (x2:nat) (y:nat)
| Dim3 (x3:nat) (y:nat) (z:nat)\<close>}
two separate selector functions \<open>x2\<close> and \<open>x3\<close> are defined where the first one is only applicable to 
two-dimensional coordinates and the second one only to three-dimensional coordinates.

If a selector name does not occur in all constructor specifications, the selector function is still
total, like all functions in Isabelle, but it is underspecified (see Section~\ref{basic-theory-terms}).
It maps values constructed by other constructors to a unique value of its result type, even if that
other constructor has no argument of this type. However, no information is available about that value.

For the type \<open>coord\<close> the selector function \<open>z :: coord \<Rightarrow> nat\<close> is also applicable to two-dimensional
coordinates, however, the values it returns for them is not specified.

Such selector values are called ``default selector values''. They may be specified in the extended
form of a datatype definition 
@{theory_text[display]
\<open>datatype name = alt\<^sub>1 | \<dots> | alt\<^sub>n
where "prop\<^sub>1" | \<dots> | "prop\<^sub>m"\<close>}
where every \<open>prop\<^sub>p\<close> is a proposition of the form
@{text[display]
\<open>sname\<^sub>i\<^sub>j (cname\<^sub>q var\<^sub>1 \<dots> var\<^sub>k\<^sub>q) = term\<^sub>p\<close>}
and specifies \<open>term\<^sub>p\<close> as the default value of selector \<open>sname\<^sub>i\<^sub>j\<close> for values constructed by \<open>cname\<^sub>q\<close>.

The definition
@{theory_text[display]
\<open>datatype coord = 
  Dim2 (x:nat) (y:nat)
| Dim3 (x:nat) (y:nat) (z:nat)
where "z (Dim2 a b) = 0"\<close>}
specifies \<open>0\<close> as default value for selector \<open>z\<close> if applied to a two-dimensional coordinate.
\<close>

subsubsection "Discriminators"

text\<open>
If an underspecified selector is applied to a datatype value it may be useful to determine which
constructor has been used to construct the value. This is supported by discriminator functions.
For every constructor specification for \<open>cname\<^sub>i\<close> the discriminator function has type \<open>name \<Rightarrow> bool\<close>
and returns true for all values constructed by \<open>cname\<^sub>i\<close>. Like selector names, discriminator names
must be explicitly specified using the extended form of a datatype definition
@{theory_text[display]
\<open>datatype name = dname\<^sub>1: alt\<^sub>1 | \<dots> | dname\<^sub>n: alt\<^sub>n\<close>}
Discriminator names may be specified for all alternatives or only for some of them. Note that for
a datatype with a single constructor the discriminator returns always \<open>True\<close> and for a datatype
with two constructors one discriminator is the negation of the other.

An example datatype definition with discriminators is
@{theory_text[display]
\<open>datatype coord =
  is_2dim: Dim2 nat nat
| is_3dim: Dim3 nat nat nat\<close>}
In a datatype definition both discriminators and selectors may be specified.
\<close>

subsubsection \<open>The {\sl case} Term\<close>

text\<open>
Additionally to using discriminators and selectors Isabelle HOL supports \<open>case\<close> terms. A \<open>case\<close>
term specifies depending on a datatype value a separate term variant for every constructor of the
datatype. In these variants the constructor arguments are available as bound variables. 

A \<open>case\<close> term for a datatype \<open>name\<close> defined as in Section~\ref{holbasic-data-def} has the form
@{text[display]
\<open>case term of 
  cname\<^sub>1 var\<^sub>1\<^sub>1 \<dots> var\<^sub>1\<^sub>k\<^sub>1 \<Rightarrow> term\<^sub>1 
| \<dots>
| cname\<^sub>n var\<^sub>n\<^sub>1 \<dots> var\<^sub>n\<^sub>k\<^sub>n \<Rightarrow> term\<^sub>n\<close>}
where \<open>term\<close> is of type \<open>name\<close> and the \<open>term\<^sub>i\<close> have an arbitrary but common type which is also the
type of the \<open>case\<close> term. In the alternative for constructor \<open>cname\<^sub>i\<close> the \<open>var\<^sub>1\<^sub>1 \<dots> var\<^sub>1\<^sub>k\<^sub>1\<close> must be 
distinct variables, they are bound to the constructor arguments and may be used in \<open>term\<^sub>i\<close> to access
them. The value of \<open>var\<^sub>i\<^sub>j\<close> is the same as the value selected by \<open>sname\<^sub>i\<^sub>j term\<close>.

If \<open>cv\<close> is a variable or constant of type \<open>coord\<close> an example \<open>case\<close> term for it is
@{text[display]
\<open>case cv of 
  Dim2 a b \<Rightarrow> a + b
| Dim3 a b c \<Rightarrow> a + b + c\<close>}
It denotes the sum of the coordinates of \<open>cv\<close>, irrespective whether \<open>cv\<close> is two-dimensional or
three-dimensional.

A \<open>case\<close> term is useful even for a datatype with a single constructor. If \<open>rv\<close> is of type \<open>recrd\<close>
as defined in Section~\ref{holbasic-data-destr} the \<open>case\<close> term
@{text[display]
\<open>case rv of MkRecrd nv sv bv \<Rightarrow> term\<close>}
makes the components of \<open>rv\<close> locally available in \<open>term\<close> as \<open>nv\<close>, \<open>sv\<close>, \<open>bv\<close>. It is equivalent to
\<open>term\<close> where \<open>nv\<close>, \<open>sv\<close>, and \<open>bv\<close> have been substituted by the selector applications \<open>(n rv)\<close>, 
\<open>(s rv)\<close>, and \<open>(b rv)\<close>.

The variant terms in a \<open>case\<close> term cannot be matched directly by a \<^theory_text>\<open>let\<close> statement in a proof (see 
Section~\ref{basic-proof-let}). The statement 
@{theory_text[display]
\<open>let "case rv of MkRecrd nv sv bv \<Rightarrow> ?t" 
   = "case rv of MkRecrd nv sv bv \<Rightarrow> term"\<close>}
will fail to bind \<open>?t\<close> to \<open>term\<close> because then the variables \<open>nv\<close>, \<open>sv\<close>, and \<open>bv\<close> would occur free
in it and the relation to the constructor arguments would be lost. Instead, the statement
@{theory_text[display]
\<open>let "case rv of MkRecrd nv sv bv \<Rightarrow> ?t nv sv bv"
   = "case rv of MkRecrd nv sv bv \<Rightarrow> term"\<close>}
successfully binds \<open>?t\<close> to the lambda term \<open>\<lambda>nv sv bv. term\<close> which denotes the function which
results in \<open>term\<close> when applied to the constructor arguments. 
\<close>

subsection "Rules"
text_raw\<open>\label{holbasic-data-rules}\<close>

text\<open>
A datatype definition also introduces a large number of named facts about the constructors and 
destructors of the defined type. All fact names belong to the namespace of the datatype definition.
Since the fact names cannot be specified explicitly, all datatype definitions use the same fact
names, therefore the fact names must always be qualified by prefixing the type name.

Several rules are configured for automatic application, e.g., they are added to the simpset for
automatic application by the simplifier (see Section~\ref{basic-methods-simp}). Other rules must
be explicitly used by referring them by their name. 

Only some basic rules are described here, for more information refer to the Isabelle documentation
about datatypes.
\<close>

subsubsection "Simplifier Rules"

text\<open>
The rules added by a datatype definition to the simpset (see Section~\ref{basic-methods-simp})
support many ways for the simplifier to process terms with constructors and destructors. An
example are equations of the form
@{text[display]
\<open>sname\<^sub>i\<^sub>j (cname\<^sub>i x\<^sub>1 \<dots> x\<^sub>k\<^sub>i) = x\<^sub>j\<close>}

The set of all rules added to the simpset is named \<open>name.simps\<close>. By displaying it using the
\<^theory_text>\<open>thm\<close> command (see Section~\ref{basic-theory-theorem}) it can be inspected to get an idea how
the simplifier processes terms for datatypes. 
\<close>

subsubsection "Case Rule"

text\<open>
Every definition for a datatype \<open>name\<close> introduces a case rule (see Section~\ref{basic-case-reasoning}) of the 
form
@{theory_text[display]
\<open>theorem name.exhaust:
  "\<lbrakk>\<And>x\<^sub>1 \<dots> x\<^sub>k\<^sub>1. y = cname\<^sub>1 x\<^sub>1 \<dots> x\<^sub>k\<^sub>1 \<Longrightarrow> P;
    \<dots> ;
    \<And>x\<^sub>1 \<dots> x\<^sub>k\<^sub>n. y = cname\<^sub>n x\<^sub>1 \<dots> x\<^sub>k\<^sub>n \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"\<close>}
It is valid because the constructor applications cover all possibilities of constructing a value
\<open>y\<close> of the datatype. 

This rule is associated with the datatype for use by the \<^theory_text>\<open>cases\<close> method
(see Section~\ref{basic-case-reasoning}). Therefore the application of the method
@{theory_text[display]
\<open>cases "term"\<close>}
where \<open>term\<close> is of type \<open>name\<close> splits an arbitrary goal into \<open>n\<close> subgoals where every subgoal uses
a different constructor to construct the \<open>term\<close>.

The names for the named contexts created by the \<^theory_text>\<open>cases\<close> method are simply the constructor names 
\<open>cname\<^sub>i\<close>. Therefore a structured proof using case based reasoning for a \<open>term\<close> of datatype \<open>name\<close>
has the form
@{theory_text[display]
\<open>proof (cases "term")
  case (cname\<^sub>1 x\<^sub>1 \<dots> x\<^sub>k\<^sub>1) \<dots> show ?thesis \<proof>
next
\<dots>
next
  case (cname\<^sub>n x\<^sub>1 \<dots> x\<^sub>k\<^sub>n) \<dots> show ?thesis \<proof>
qed\<close>}
The names \<open>x\<^sub>i\<close> of the locally fixed variables can be freely selected, they denote the constructor
arguments of the corresponding constructor. Therefore the case specification \<open>(cname\<^sub>i x\<^sub>1 \<dots> x\<^sub>k\<^sub>i)\<close>
looks like a constructor application to variable arguments, although it is actually a context name
together with locally fixed variables.
\<close>

subsubsection "Split Rule"

text\<open>
A \<open>case\<close> term (see Section~\ref{holbasic-data-destr}) is only processed be the simplifier, if a
corresponding split rule is configured for it (see Section~\ref{basic-methods-simp}). Every definition
for a datatype \<open>name\<close> introduces such a split rule. It has the form
@{theory_text[display]
\<open>theorem name.split:
  "P(case term of 
      cname\<^sub>1 var\<^sub>1\<^sub>1 \<dots> var\<^sub>1\<^sub>k\<^sub>1 \<Rightarrow> term\<^sub>1 
    | \<dots>
    | cname\<^sub>n var\<^sub>n\<^sub>1 \<dots> var\<^sub>n\<^sub>k\<^sub>n \<Rightarrow> term\<^sub>n) = 
  (   (term = cname\<^sub>1 var\<^sub>1\<^sub>1 \<dots> var\<^sub>1\<^sub>k\<^sub>1 \<longrightarrow> P(term\<^sub>1))
    \<and> \<dots>
    \<and> (term = cname\<^sub>n var\<^sub>n\<^sub>1 \<dots> var\<^sub>n\<^sub>k\<^sub>n \<longrightarrow> P(term\<^sub>n)))"\<close>}
As described in Section~\ref{basic-methods-simp} it splits a goal with a \<open>case\<close> term for type \<open>name\<close>
in the conclusion into goals where the \<open>case\<close> term is replaced by the \<open>term\<^sub>i\<close>.

As an example, let \<open>cv\<close> be a variable or constant of type \<open>coord\<close>, as above. Then the goal
@{text[display]
\<open>sum = (case cv of Dim2 a b \<Rightarrow> a + b | Dim3 a b c \<Rightarrow> a + b + c)\<close>}
is split by the split rule \<open>coord.split\<close> into the goals
@{text[display]
\<open>cv = Dim2 a b \<Longrightarrow> sum = a + b
cv = Dim3 a b c \<Longrightarrow> sum = a + b + c\<close>}
\<close>

subsubsection "Induction Rule"

text\<open>
Every definition for a datatype \<open>name\<close> introduces an induction rule (see Section~\ref{basic-case-induction})
of the form
@{theory_text[display]
\<open>theorem name.induct:
  "\<lbrakk>\<And>x\<^sub>1 \<dots> x\<^sub>k\<^sub>1. \<lbrakk>?P x\<^sub>l\<^sub>1; \<dots> ?P x\<^sub>l\<^sub>m\<^sub>1\<rbrakk> \<Longrightarrow> ?P (cname\<^sub>1 x\<^sub>1 \<dots> x\<^sub>k\<^sub>1);
    \<dots> ;
    \<And>x\<^sub>1 \<dots> x\<^sub>k\<^sub>n. \<lbrakk>?P x\<^sub>l\<^sub>n; \<dots> ?P x\<^sub>l\<^sub>m\<^sub>n\<rbrakk> \<Longrightarrow> ?P (cname\<^sub>n x\<^sub>1 \<dots> x\<^sub>k\<^sub>n)\<rbrakk>
   \<Longrightarrow> ?P ?a"\<close>}
where the \<open>x\<^sub>l\<^sub>1 \<dots> x\<^sub>l\<^sub>m\<^sub>i\<close> are those \<open>x\<^sub>1 \<dots> x\<^sub>k\<^sub>i\<close> which have type \<open>name\<close> (i.e., the recursive
occurrences of the type name). Like the case rule it is valid because the constructor applications 
cover all possibilities of constructing a value \<open>?a\<close> of the datatype.

If the datatype \<open>name\<close> is not recursive there are no \<open>x\<^sub>l\<^sub>1 \<dots> x\<^sub>l\<^sub>m\<^sub>i\<close> and the assumptions of all
inner rules are empty, then the induction rule is simply a specialization of the case rule and is
redundant. However, for a recursive datatype \<open>name\<close> induction using rule \<open>name.induct\<close> is the
standard way of proving a property to hold for all values.

The rule \<open>name.induct\<close> is associated with datatype \<open>name\<close> for use by the methods \<^theory_text>\<open>induction\<close> and
\<^theory_text>\<open>induct\<close> (see Section~\ref{basic-case-induction}). Therefore the application of the method
@{theory_text[display]
\<open>induction x\<close>}
where \<open>x\<close> is a variable of type \<open>name\<close> splits a goal into \<open>n\<close> subgoals where every subgoal uses
a different constructor term in the place of \<open>x\<close> in its conclusion.

As for the case rule and the \<^theory_text>\<open>cases\<close> method, the names for the named contexts created by the 
methods \<^theory_text>\<open>induction\<close> and \<^theory_text>\<open>induct\<close> are simply the constructor names \<open>cname\<^sub>i\<close>. Therefore a structured
proof using induction for a variable \<open>x\<close> of datatype \<open>name\<close> has the form
@{theory_text[display]
\<open>proof (induction x)
  case (cname\<^sub>1 x\<^sub>1 \<dots> x\<^sub>k\<^sub>1) \<dots> show ?case \<proof>
next
\<dots>
next
  case (cname\<^sub>n x\<^sub>1 \<dots> x\<^sub>k\<^sub>n) \<dots> show ?case \<proof>
qed\<close>}

In the rule \<open>name.induct\<close> all inner assumptions are of the form \<open>?P x\<^sub>l\<^sub>i\<close>, i.e., they are induction
hypotheses and are named \<open>"cname\<^sub>i.IH"\<close> by the \<^theory_text>\<open>induction\<close> method, the assumption set \<open>"cname\<^sub>i.hyps"\<close>
is always empty. The \<^theory_text>\<open>induct\<close> method instead names all inner assumptions by \<open>"cname\<^sub>i.hyps"\<close>.

As an example, the induction rule for the recursive datatype \<open>tree\<close> defined in 
Section~\ref{holbasic-data-def} is
@{theory_text[display]
\<open>theorem tree.induct:
  "\<lbrakk>\<And>x. ?P (Leaf x);
    \<And>x\<^sub>1 x\<^sub>2 x\<^sub>3. \<lbrakk>?P x\<^sub>2; ?P x\<^sub>3\<rbrakk> \<Longrightarrow> ?P (Tree x\<^sub>1 x\<^sub>2 x\<^sub>3)\<rbrakk>
   \<Longrightarrow> ?P ?a"\<close>}
If \<open>p :: tree \<Rightarrow> bool\<close> is a predicate function for values of type \<open>tree\<close> the goal \<open>p x\<close> which states
that \<open>p\<close> holds for all values is split by applying the method \<open>(induction x)\<close> into the goals
@{text[display]
\<open>\<And>x. p (Leaf x)
\<And>x\<^sub>1 x\<^sub>2 x\<^sub>3. \<lbrakk>p x\<^sub>2; p x\<^sub>3\<rbrakk> \<Longrightarrow> p (Tree x\<^sub>1 x\<^sub>2 x\<^sub>3)\<close>}

A structured proof for goal \<open>p x\<close> has the form
@{theory_text[display]
\<open>proof (induction x)
  case (Leaf x) \<dots> show ?case \<proof>
next
  case (Tree x\<^sub>1 x\<^sub>2 x\<^sub>3) \<dots> show ?case \<proof>
qed\<close>}
and in the second case the assumptions \<open>p x\<^sub>2, p x\<^sub>3\<close> are named \<open>Tree.IH\<close>.
\<close>

section "Record Types"
text_raw\<open>\label{holbasic-record}\<close>

text\<open>
**todo**
\<close>

section "Subtypes"
text_raw\<open>\label{holbasic-sub}\<close>

text \<open>
A subtype specifies the values of a type simply as a set of values of an existing type. However,
since the values of different types are always disjoint, the values in the set are not directly the
values of the new type, instead, there is a 1-1 relation between them, they are isomorphic. The 
values in the set are called ``representations'', the values in the new type are called ``abstractions''.\<close>

subsection "Subtype Definitions"
text_raw\<open>\label{holbasic-sub-def}\<close>

text \<open>
A subtype is defined in the form
@{theory_text[display]
\<open>typedef name = "term" \<proof>\<close>}
where \<open>name\<close> is the name of the new type and \<open>term\<close> is a term for the representing set. See 
Section~\ref{holtypes-set} for how to denote such terms. The \<open>\<proof>\<close> must prove that the 
representing set is not empty. 

A simple example is the type\<close>
typedef three = "{1::nat,2,3}" by auto
text \<open>
which has three values. The representations are natural numbers, as usual, the type \<open>nat\<close> must be
specified because the constants \<open>1, 2, 3\<close> may also denote values of other types. However, they do
not denote the values of the new type \<open>three\<close>, the type definition does not introduce constants
for them.

Instead, a subtype definition \<^theory_text>\<open>typedef t = "term" \<proof>\<close> introduces two functions \<open>Abs_t\<close>
and \<open>Rep_t\<close>. These are morphisms between the set and the new type, \<open>Abs_t\<close> maps from the set 
to type \<open>t\<close>, \<open>Rep_t\<close> is its inverse. Both functions are injective, together they provide the
1-1 mapping between the subtype and the representing set. The function \<open>Abs_t\<close> can be used to
denote the values of the subtype.

In the example the morphisms are \<open>Abs_three :: nat \<Rightarrow> three\<close> and \<open>Rep_three :: three \<Rightarrow> nat\<close>. The
values of type \<open>three\<close> may be denoted as \<open>(Abs_three 1)\<close>, \<open>(Abs_three 2)\<close>, and \<open>(Abs_three 3)\<close>.

Alternative names may be specified for the morphisms in the form
@{theory_text[display]
\<open>typedef t = "term" morphisms rname aname \<proof>\<close>}
where \<open>rname\<close> replaces \<open>Rep_t\<close> and \<open>aname\<close> replaces \<open>Abs_t\<close>.

Like declared types subtypes may be parameterized (see Section~\ref{basic-theory-types}):
@{theory_text[display]
\<open>typedef ('name\<^sub>1,\<dots>,'name\<^sub>n) name = "term" \<proof>\<close>}
where the \<open>'name\<^sub>i\<close> are the type parameters. They may occur in the type of the \<open>term\<close>, i.e., the 
\<open>term\<close> may be polymorphic (see Section~\ref{basic-theory-terms}).
\<close>

subsection "Subtype Rules"
text_raw\<open>\label{holbasic-sub-rules}\<close>

text\<open>
**todo**
\<close>

section "Quotient Types"
text_raw\<open>\label{holbasic-quot}\<close>

text\<open>
**todo**
\<close>

section "Type Independent Mechanisms"
text_raw\<open>\label{holbasic-common}\<close>

text\<open>
This section describes some mechanisms introduced by HOL which can be used for all types.
\<close>

subsection "Equality"
text_raw\<open>\label{holbasic-common-equal}\<close>

text\<open>
HOL introduces the equality predicate as a function
@{text[display]
\<open>eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool"\<close>}
with the alternative operator symbol \<open>=\<close> for infix notation.

Inequality can be denoted by
@{text[display]
\<open>not_equal :: "'a \<Rightarrow> 'a \<Rightarrow> bool"\<close>}
with the alternative operator symbol \<open>\<noteq>\<close> for infix notation.

Both functions are overloaded and can be applied to terms of arbitrary type, however, 
they can only be used to compare two terms which have the same type. Therefore the
proposition
@{text[display]
\<open>True \<noteq> 1\<close>}
is syntactically wrong and Isabelle will signal an error for it.
\<close>

subsection "Undefined Value"
text_raw\<open>\label{holbasic-common-undefined}\<close>

text\<open>
HOL introduces the undefined value
@{text[display]
\<open>undefined :: "'a"\<close>}
which is overloeaded for arbitrary types. It is underspecified as described in
Section~\ref{basic-theory-terms}, i.e., no further information is given about it.

Despite its name it is a well defined value for every type \<open>'a\<close>. It is typically used for 
values which are irrelevant, such as in the definition\<close>
definition f :: "nat \<Rightarrow> nat" where "f x \<equiv> undefined"
text\<open>
Although the function \<open>f\<close> looks like a completely undefined function, it is not possible to define
true partial functions this way. Functions in Isabelle are always total. Function \<open>f\<close> maps every
natural number to the (same) value \<open>undefined\<close>, which is of type \<open>nat\<close>, but it cannot be proven to
be equal to a specific natural number such as \<open>1\<close> or \<open>5\<close>. However, since it is a single value the
following equality holds:
\<close>
lemma "f x = f y" by (simp add: f_def)

subsection "Let Terms"
text_raw\<open>\label{holbasic-common-let}\<close>

text\<open>
HOL extends the inner syntax for terms described in Section~\ref{basic-theory-terms} by terms of
the following form
@{text[display]
\<open>let x\<^sub>1 = term\<^sub>1; \<dots>; x\<^sub>n = term\<^sub>n in term\<close>}
where \<open>x\<^sub>1, \<dots>, x\<^sub>n\<close> are variables. The variable bindings are sequential, i.e., if \<open>i<j\<close> variable
\<open>x\<^sub>i\<close> may occur in \<open>term\<^sub>j\<close> and denotes \<open>term\<^sub>i\<close> there. In other words, the scope of \<open>x\<^sub>i\<close> are the 
terms \<open>term\<^sub>j\<close> with \<open>i<j\<close> and the \<open>term\<close>. If \<open>x\<^sub>i\<close> and \<open>x\<^sub>j\<close> are the same variable, the binding of 
its second occurrence shadows the binding of the first and ends the scope of the first occurrence.

Let terms are useful to introduce local variables as abbreviations for sub-terms.

The let term specified above is simply an alternative syntax for the term
@{text[display]
\<open>\<lambda>x\<^sub>1.(\<dots> (\<lambda>x\<^sub>n.term) term\<^sub>n \<dots>) term\<^sub>1\<close>}
\<close>

(*
???
subsection "Lifting and Transfer"
text_raw\<open>\label{holbasic-common-lift}\<close>
*)

end