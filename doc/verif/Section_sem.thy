theory Section_sem
  imports Main

begin
section "Function Semantics"
text_raw\<open>\label{verif-sem}\<close>

text \<open>
The formal specification generated by the Cogent compiler (the ``shallow embedding'') consists of three 
theory files. For each Cogent program a specific prefix \code{X} is used in the theory names.
As described in Section~\ref{impl-isabelle-shallow} the file \code{X\_Shallow\_Desugar\_Tuples.thy} 
contains the definitions for all non-abstract functions defined in the Cogent program. The function
names are the same as those used in the Cogent program. Additionally
it contains definitions for functions corresponding to all lambda terms used in the Cogent program, 
where the function names are automatically generated.

These function definitions strictly reflect the Cogent function definitions in the following ways
\begin{itemize}
\item Functions invoked by a function \code{f} in Cogent are also invoked by \code{f} in the shallow
embedding. These may either be defined functions or abstract functions. For abstract functions the 
generated theory \code{X\_ShallowShared\_Tuples.thy} contains declarations as Isabelle ``constants''
specifying the name and the type.
\item Operations on Cogent record and tuple types are represented by equivalent operations on HOL record 
and tuple types.
\item Cogent control structures like \code{let}, \code{if}, and \code{match} expressions are represented
by corresponding HOL control functions (\code{let}, \code{if}, and \code{case}).
\end{itemize}
The main differences are that matching with complex patterns in Cogent is resolved to matching single
variables in the shallow embedding and that the shallow embedding may use additional bindings to auxiliary 
variables.

The generated shallow embedding must be complemented by HOL definitions of all abstract functions used
in the Cogent program. Since Cogent generates declarations for them, their definitions must either be provided
as axioms or by overloading.

Note that invoked abstract functions also cover operations on data types other than primitive and struct 
types (see Section~\ref{design-operations}) and loop control structures (see Section~\ref{design-??}).
Since we assume that the Cogent function definition has been generated by Gencot from the C source, 
Gencot also generates HOL definitions for these abstract functions. Together, the 
functions in the shallow embedding strongly reflect the steps used in C programs to implement tasks.

The goal of the function semantics is to provide an alternative definition (a ``semantics'') for all 
(abstract and non-abstract) functions and prove its equivalence with the original definition. 
The semantics is defined using HOL functions for working with the data structures resulting from
translating a Gencot-generated Cogent program. Gencot provides a rich collection of such functions, so
that the semantics definitions can achieve the following properties:
\begin{itemize}
\item Every semantics does not use any of the defined or abstract functions
from the Cogent program and can be regarded as a ``pure'' standalone HOL description of the function.
\item Sequential observations and modifications of data structure parts are aggregated to parallel 
observations and modifications of the whole data structure. In particular, loops for processing
arrays are replaced by bulk operations on arrays. 
\item ``Explicit'' modifications of data structure parts, where the old value is accessed, modified, 
and then inserted at the same place, are replaced by ``implicit'' modifications, where the modification
is specified by a modification function to be mapped to the part.
\end{itemize}

Gencot provides such semantics for all abstract functions implementing its basic operations, either 
by defining a semantics and proving equivalence to the provided function definition, or by directly
defining the function in the form described above.
\<close>

subsection "HOL Types for Semantics Specifications"
text_raw\<open>\label{verif-sem-types}\<close>

text \<open>
The functions used to specify the semantics have to deal with values of the types defined in the Cogent program.
The nonprimitive Cogent types are translated by the Cogent compiler to Isabelle as follows.
\begin{itemize}
\item Cogent record types are translated to HOL record types where field names get an index \<open>f\<close> appended,
thus \code{name} becomes \<open>name\<^sub>f\<close>.
\item Cogent tuple types are translated to HOL tuple types.
\item Gencot array types are translated to HOL record types which contain a single field for a HOL list.
The record type is generic for the element type, but it is specific for the array size, which is achieved
by encoding the array size in the field name, as described in Sections~\ref{design-types-array}
and \ref{design-isabelle-types}.
Gencot provides support for these types as described in Section~\ref{design-isabelle-gencotrul}.
\item Gencot pointer types are translated to HOL record types which contain a single field of the type
referenced by the pointer. The field always has the name \<open>cont\<^sub>f\<close>, as described in Section~\ref{design-types-pointer}.
\item Gencot array pointer types of the form \code{CArrPtr el} used for explicitly sized arrays 
(see Section~\ref{design-operations-esarray}) are directly translated to the HOL list type \<open>'el list\<close>, 
generic for the element type.
\item Gencot types of the form \code{(MayNull a)} are translated to option types of the form \<open>'a option\<close>.
\end{itemize}

Therefore the functions for semantics specification mainly work with HOL records, tuples, and lists. 
Since in C arrays are naturally viewed as partial mappings from index values to element values, 
Gencot also provides functions for HOL map types of the form \<open>A \<rightharpoonup> B\<close>.
\<close>

subsection "Functions for Semantics Specification"
text_raw\<open>\label{verif-sem-fun}\<close>

text \<open>
According to their type, we classify the functions for semantics specification into \textit{construction functions},
\textit{observation functions}, and \textit{modification functions}.
\<close>

subsubsection "Construction Functions"

text \<open>
A function \<open>f\<close> is a \textbf{construction function for a type} \<open>T\<close> if it has the type \<open>A \<Rightarrow> T\<close> for some 
type \<open>A\<close> or is a constant of type \<open>T\<close>.
\<close>

subsubsection "Observation Functions"

text \<open>
A function \<open>f\<close> is an \textbf{observation function for a type} \<open>T\<close> (also called a \textit{projection})
if it has the type \<open>T \<Rightarrow> A\<close> for some 
type \<open>A\<close>. An observation function need neither be surjective nor injective. If it is not injective it
is an ``abstracting'' observation which discards some information about the observed values.

Two observation functions \<open>f :: T \<Rightarrow> A\<close> and \<open>g :: T \<Rightarrow> B\<close> can be combined to a new observation function
by an injective combination function \<open>c :: A \<Rightarrow> B \<Rightarrow> C\<close>. The combined observation is 
\<open>(obscmb c f g) :: T \<Rightarrow> C\<close> which is defined by \<open>(obscmb c f g) x \<equiv> c (f x) (g x)\<close>. Since \<open>c\<close> is injective
the single observations can always be retrieved from the combined observation. Useful combination functions
are the HOL pairing function \<open>Pair\<close> or every HOL record construction function \<open>make\<close> for a record with
two components. In the former case the combined observation is a function
\<open>(f\<times>g) :: T \<Rightarrow> (A\<times>B)\<close> defined by \<open>(f\<times>g)(x) \<equiv> (f x, g x)\<close>, which returns the pair of observation values. 
Usually, a combined observation is ``less abstract'' than the single observations, because it returns 
more information about the observed values. 

The observations \<open>f\<close> and \<open>g\<close>
are \textbf{independent} if \<open>range (f\<times>g) = (range f) \<times> (range g)\<close>, i.e. if for every value of \<open>f\<close> 
function \<open>g\<close> can observe all its possible values and vice versa.

If the result type \<open>A\<close> of an observation function \<open>f :: T \<Rightarrow> A\<close> is again a data structure with an observation 
function \<open>g :: A \<Rightarrow> B\<close>, the composition \<open>g\<circ>f :: T \<Rightarrow> B\<close> is an observation function for type \<open>T\<close>. A typical
case where this occurs are nested data structures, where a structure of type \<open>A\<close> is nested in a structure
of type \<open>T\<close>.

Basic observation functions for HOL records are the field access functions which are automatically provided 
by HOL for each defined record type. Functions for different fields are independent observations.
The basic observation function for HOL lists is function 
\<open>nth :: 'el list \<Rightarrow> nat \<Rightarrow> 'el\<close> with the abbreviation \<open>(nth l i) = (l ! i)\<close>. Gencot provides the function
\<open>elm :: nat \<Rightarrow> 'el list \<Rightarrow> 'el\<close> with swapped arguments, so that for every index \<open>i\<close> the function
\<open>(elm i)\<close> is an observation function on lists. If \<open>i\<noteq>j\<close> the observations \<open>(elm i)\<close> and \<open>(elm j)\<close> are
independent. Independent basic observation functions for HOL pairs are the HOL functions
\<open>fst\<close> and \<open>snd\<close> which return the first and second component, respectively. For larger tuples Gencot 
provides observation functions \<open>fstOf<n>\<close>, \<open>sndOf<n>\<close>, \<open>thdOf<n>\<close>, \<open>frtOf<n>\<close>, \<open>fifOf<n>\<close>, and \<open>sixOf<n>\<close>
for \<open><n>\<close> ranging from \<open>2\<close> to \<open>6\<close>, where \<open>fstOf2 = fst\<close>, \<open>sndOf2 = snd\<close>, and so on.
\<close>

subsubsection "Modification Functions"

text \<open>
A function \<open>f\<close> is a \textbf{modification function for a type} \<open>T\<close> (also called an \textit{update function})
if it has the type \<open>T \<Rightarrow> T\<close>. A modification function need neither be surjective nor injective. 

For an observation function \<open>o :: T \<Rightarrow> A\<close> the \textit{part update function for} \<open>o\<close> is a function 
\<open>m :: (A\<Rightarrow>A) \<Rightarrow> T \<Rightarrow> T\<close> which takes a modification function for type \<open>A\<close> as its argument and satisfies
the following laws:
\begin{enumerate}
\item \<open>o (m u x) = u (o x)\<close>
\item \<open>(m id) = id\<close>
\item \<open>(m u1) \<circ> (m u2) = m (u1 \<circ> u2)\<close>
\item \<open>m u x = m (\<lambda>_. u (o x)) x\<close>
\end{enumerate}
According to (1) it modifies the observation by applying \<open>u\<close> to it. According to (2) it does not modify 
any other part. According to (3) it can be chained by chaining the modification functions for the observation.
According to (4) it takes no other information into account than the modified observation. For every
modification function \<open>u\<close> for type \<open>A\<close> the function \<open>(m u)\<close> is a modification function for type \<open>T\<close>.
The laws (2) and (3) imply that type \<open>T\<close> is a functor for type \<open>A\<close> and \<open>m\<close> is a ``functorial action'' 
or ``mapping function'' for it. A part update function need not exist for arbitrary observation functions.

Gencot provides support for part update functions in theory \<open>Gencot_PartAccess\<close>. It defines the type 
constructor \<open>PartUpdate\<close> with  \<open>(T,A) PartUpdate = (A\<Rightarrow>A) \<Rightarrow> T \<Rightarrow> T\<close> and it defines the locale
\<open>PartUpdate\<close> which introduces instances of laws (2) and (3) for a function \<open>m\<close> and the locale \<open>PartAccess\<close>
which additionally introduces instances of laws (1) and (4) for a pair of functions \<open>o\<close> and \<open>m\<close>.

If two observations \<open>o1 :: T \<Rightarrow> A\<close> and \<open>o2 :: A \<Rightarrow> B\<close> have part update functions \<open>m1 :: (T,A) PartUpdate\<close>
and \<open>m2 :: (A,B) PartUpdate\<close> the composition \<open>m1\<circ>m2\<close> is a part update function for the composed 
observation \<open>o2\<circ>o1\<close> (note the reversed order of composition).

If two independent observations \<open>o1 :: T \<Rightarrow> A\<close> and \<open>o2 :: T \<Rightarrow> B\<close> have part update functions 
\<open>m1 :: (T,A) PartUpdate\<close> and \<open>m2 :: (A,B) PartUpdate\<close> the following additional laws are satisfied:
\begin{enumerate}\setcounter{enumi}{5}
\item \<open>o1 \<circ> (m2 u) = o1\<close>
\item \<open>(m1 u1) \<circ> (m2 u2) = (m2 u2) \<circ> (m1 u1)\<close> 
\end{enumerate}
According to (5) observation \<open>o1\<close> absorbs modification \<open>m2\<close> (by symmetry also \<open>o2\<close> absorbs \<open>m1\<close>). 
According to (6) modifications \<open>m1\<close> and \<open>m2\<close> commute.

Gencot provides support for these laws by defining the locale \<open>PartComm\<close> which introduces an instance
of law (6) for two part update functions \<open>m1\<close> and \<open>m2\<close>, and the locale \<open>PartAbsrb\<close> which introduces
an instance of law (5) for two pairs of observations and part update functions \<open>o1,m1\<close> and \<open>o2,m2\<close>.

For every HOL record field access function \<open>fld\<close> the part update function is \<open>fld_update\<close> which is 
also automatically provided by HOL. For every list element access function \<open>(elm i)\<close> Gencot provides 
the part update function \<open>(elm_update i)\<close>. 
\<close>

subsection "Arrays and Wellsizedness"
text_raw\<open>\label{verif-sem-wlsd}\<close>

text \<open>
In C most arrays have a known size, either specified as part of its type, or stored somewhere in the
context where it can be retrieved when the array is processed. The array size is used for array
processing, such as as a limit for loops or as a comparison value when testing whether an index is
valid. In the shallow embedding arrays are represented as lists of arbitrary length, therefore the
size information is not available.

Gencot supports C arrays generically in theory \<open>Gencot_CArray_Lemmas\<close>. A C array is an arbitrary type
\<open>carray\<close> with two observations: a function \<open>arr :: carray \<Rightarrow> 'el list\<close> for the representing list 
and the function \<open>siz :: carray \<Rightarrow> nat\<close> for the array size. 
\<close>

subsubsection "Array Wellsizedness"

text \<open>
For all correct representations of C arrays the length of the list must equal the array size. 
Additionally, Gencot does not support empty arrays, so the array size must not be zero. Gencot
defines the predicate \<open>wlsd :: carray \<Rightarrow> bool\<close> (``wellsized'') to express these properties. 
Wellsizedness is a special case of the general notion of wellformedness. This
approach covers the C array types as described in Section~\ref{design-types-array} as well as the
explicitly sized arrays (see Section~\ref{design-types-esarray} and self-descriptive and externally 
described arrays (see Section~\ref{app-transtype-arrpoint}). 

Gencot provides support for C array types and explicitly sized arrays. Other arrays 
are program specific, support for them must be provided manually. For C array types with a fixed 
size Gencot defines the locale \<open>FxdArrSemantics\<close> which sets up the support for all arrays of a 
specific size, and interpretes it for every array size occurring in the translated program.
\<close>

subsubsection "Generalized Wellsizedness"

text \<open>
C arrays may be nested in other data structures, a data structure may contain several different
arrays and arrays may be nested in elements of other arrays. For every data structure which contains
one or more arrays, all of them must be wellsized. To express this property it is recommended to
define an according generalized wellsizedness predicate for all data structures which contain atleast
one array.

Since the data structures are program specific this must be done manually.

In a correct C program the generalized wellsizedness must hold for every data structure at every 
moment in time (with the exception of time spans where the array size is changed (e.g. by allocating 
more memory) and the stored size must be updated or, for self-described arrays, the content must 
be adapted to the new size). This property also holds for all values in a Cogent program which results
from a translation by Gencot, and for every value in the shallow embedding. Thus, wellsizedness can
be assumed for every otherwise unknown value in the shallow embedding, in particular, for all 
arguments of the Cogent functions. 

This allows to always derive the length of all lists used for representing arrays. It is an important
prerequisite when specifying the semantics for Cogent functions which process arrays, since it is
required for proving, e.g., that a loop actually processes the whole array and is equivalent to a 
bulk operation for the representing list. Therefore, semantics specification theorems usually have
wellsizedness premises for all arguments which contain arrays.
\<close>

subsubsection "Wellsizedness Preservation"

text \<open>
In a correct C program all primitive array modification operations preserve wellsizedness. For arrays 
specified by an array type with a fixed size they do not modify the array size. For other arrays, 
whenever the size changes the associated size specification is updated.

This implies that all other modification functions which are built from these primitive operations
also preserve (generalized) wellsizedness for all their arguments. The same holds for the Cogent functions
resulting from a translated C program and for their shallow embedding form and their semantics. If two
such functions are composed, the semantics of the second function can only be substituted if the 
wellsizedness premise for its argument has been proved, which means to prove that the first function 
must preserve wellsizedness. 

Moreover, the property that every function which modifies data structures with arrays preserves wellsizedness
is an important correctness property for the translated C program, so its proof is a relevant part
of the correctness prove for the program.

Therefore it is recommended to provide wellsizedness preservation proofs for all Cogent functions in
the shallow embedding, which modify data structures with arrays. In the simplest case the corresponding 
proposition for a function \<open>f\<close> has the form \<open>wlsd x \<Longrightarrow> wlsd (f x)\<close>. If \<open>f\<close> takes an argument tuple and 
returns a result tuple where one component contains arrays the proposition has the form
\<open>wlsd x \<Longrightarrow> wlsd (sel (f (x1,...,x,...,xn)))\<close> where \<open>sel\<close> is one of the tuple selector functions
like \<open>thdOf<n>\<close>. Alternatively, generalized wellsizedness predicates can be defined for the argument
and result tuples and the simpler form above can be used. This may be useful if several functions have
argument and/or result tuples of the same type.
\<close>

subsubsection "Wellsizedness Preservation for Part Update Funćtions"

text \<open>
If \<open>m\<close> is a part update function for an observation \<open>o\<close> which contains arrays, \<open>(m u)\<close> only preserves
wellsizedness if \<open>u\<close> does for the part. Since \<open>u\<close> is not applied to an argument, wellsizedness 
preservation for \<open>m\<close> cannot be specified as described above. 

Therefore Gencot provides the predicate \<open>prsvwlsd :: ('x \<Rightarrow> 'x) \<Rightarrow> bool\<close> for modification functions
defined by \<open>prsvwlsd f \<equiv> \<forall>x. wlsd x \<longrightarrow> wlsd (f x)\<close>. Now the wellsizedness preservation proposition 
for a part update function can be specified as
\<open>prsvwlsd u \<Longrightarrow> prsvwlsd (m u)\<close>. The predicate can also be used to specify wellsizedness preservation
for arbitrary modification functions \<open>f\<close> as \<open>prsvwlsd f\<close> or, with tuples as argument and result as
\<open>prsvwlsd (\<lambda>x. sel (f (x1,...,x,...,xn)))\<close>.
\<close>

subsubsection "Automatic Wellsizedness Deduction"

text \<open>
Gencot provides support for defining a set of rules so that the simplifier can deduce all relevant
wellsizedness propositions automatically. 

There are two main kinds of such propositions: wellsizedness propositions for observations and 
wellsizedness propositions for modification results.

If for an observation function \<open>o :: T \<Rightarrow> A\<close> the result type contains arrays it must be possible 
to deduce \<open>wlsd x \<Longrightarrow> wlsd (o x)\<close>, in particular, if the result type \<open>A\<close> is a C array type. The proof
is usually done by unfolding the definition of \<open>o\<close> and the \<open>wlsd\<close> predicate for type \<open>T\<close>.
For every C array type it must be possible to deduce \<open>wlsd x \<Longrightarrow> length (arr x) = siz x\<close> which follows
from the definition of \<open>wlsd\<close>. Together these rules allow to deduce the length of all array 
representation lists from wellsizedness premises for Cogent function arguments. The corresponding 
rules must be specified for every observation function \<open>o\<close> and for every C array type, they should 
be added directly to the simpset.

If for a modification function \<open>m :: T \<Rightarrow> T\<close> the type \<open>T\<close> contains arrays it must be possible to
deduce \<open>wlsd x \<Longrightarrow> wlsd (m x)\<close>, i.e., wellsizedness preservation. It is required for wellsizedness
premises of semantics rules, if the argument is the result of applying a modification function.
This deduction is mainly supported by rules of the form  \<open>\<lbrakk>wlsd x; prsvwlsd m\<rbrakk> \<Longrightarrow> wlsd (m x)\<close>
and rules for deducing \<open>prsvwlsd m\<close>. 

Gencot provides a rule bucket \<open>wlsd\<close> for collecting such rules and it provides locales \<open>Wlsd\<close> and
\<open>Prsvwlsd\<close> for generating the rules and inserting them into the bucket. The \<open>Wlsd\<close> locale must be 
interpreted for every wellsizedness predicate, the \<open>Prsvwlsd\<close> locale must be interpreted for every
modification function \<open>m\<close> for a type with arrays. Additionally, for every modification function \<open>m\<close>
a rule for deducing wellsizedness preservation must be specified and inserted in the bucket. For 
construction functions a rule must be specified, that the result is always wellsized. Gencot
provides locales \<open>PrsvwlsdAlways\<close>, \<open>PrsvwlsdIfpart\<close> for the most common cases. The bucket must be 
added to the simplifier whenever wellsizedness deduction involves modification functions.

If arrays nested in other arrays are involved, additional rules are required which deduce properties
for all elements of a list. Gencot provides the bucket \<open>lstp\<close> for these rules and it provides the 
locale \<open>PrsvwlsdIfarr\<close> which puts the rules into the bucket and must be interpreted for every 
C array part update function \<open>m :: (carray,'el list) PartUpdate\<close> which modifies the array by 
modifying the representing list. The bucket must be added together with \<open>wlsd\<close> to the simplifier,
whenever wellsizedness deduction involves modification functions and nested arrays.
\<close>

subsection "Semantics Specification"
text_raw\<open>\label{verif-sem-spec}\<close>

subsubsection "Semantics Theorems"

subsubsection "Wellformedness Preservation"

subsubsection "Semantics for Abstract Functions"

subsection "Proving Semantics Specification"
text_raw\<open>\label{verif-sem-proof}\<close>

subsubsection "Proving Record Operations"

subsubsection "Proving Array Operations"

subsubsection "Proving Loop Semantics"

end
