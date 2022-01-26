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

Note that invoked abstract functions also cover operations on data types other than primitive and struct 
types (see Section~\ref{design-operations}) and loop control structures (see Section~\ref{design-??}).
Since we assume that the Cogent function definition has been generated by Gencot from the C source, the 
functions in the shallow embedding strongly reflect the steps used in C programs to implement tasks.

The goal of this section is to define a small set of functions using the features and types provided by HOL
so that they can be used to specify an alternative definition (a ``semantics'') for all functions in the 
shallow embedding. In particular, the semantics does not use any of the defined or abstract functions
from the Cogent program and can be regarded as a ``pure'' HOL description of the function.
\<close>

subsection "Functions for Semantics Specification"
text_raw\<open>\label{verif-sem-fun}\<close>

text \<open>
The functions defined in the Cogent program may take arguments of several different types and return 
results of several different types. The functions used for expressing their semantics are intended to 
be instead type specific, so that they together constitute an abstract data type for the related type.
These functions may either be standard HOL functions, or functions provided
by Gencot, or functions specifically defined for a type introduced in the Cogent program. Gencot also
provides support for defining program specific functions for several standard cases of using C data 
structures.

According to their type, we classify the functions for semantics specification into \textit{observation
functions} and \textit{construction functions}.
\<close>

subsubsection "HOL Types for Semantics Specifications"

text \<open>
The semantic specification functions have to deal with values of the types defined in the Cogent program.
The nonprimitive Cogent types are translated by the Cogent compiler to Isabelle as follows.
\begin{itemize}
\item Cogent record types are translated to HOL record types where field names get an index \<open>f\<close> appended,
thus \code{name} becomes \<open>name\<^sub>f\<close>.
\item Cogent tuple types are translated to HOL tuple types.
\item Gencot array types are translated to HOL record types which contain a single field of a HOL list type
of fixed length. Gencot provides support for these types as described in Section~\ref{design-isabelle-gencotrul}.
\item Gencot pointer types are translated to HOL record types which contain a single field of the type
referenced by the pointer. The field always has the name \<open>cont\<^sub>f\<close>.
\item Gencot array pointer types used for explicitly sized arrays (see Section~\ref{design-operations-esarray})
are translated to HOL record types with a single field of the HOL list type. The field always has the name 
\<open>arr\<^sub>f\<close>.
\item Gencot types of the form \code{(MayNull a)} are translated to option types of the form \<open>'a option\<close>.
\end{itemize}

For abstractions of these types the following HOL types may be useful, among others:
\begin{itemize}
\item Map types of the form \<open>A \<rightharpoonup> B\<close>
\end{itemize}
\<close>


subsubsection "Observation Functions"

text \<open>
A function $f$ is an \textbf{observation function for a type} $T$ if it has the type $f: T \to A$ for some 
type $A$. An observation function need neither be surjective nor injective. If it is not injective it
is an ``abstracting'' observation which discards some information about the observed values.

Two observation functions $f: T\to A$ and $g: T\to B$ can be combined to a new observation function 
$(f\times g): T \to A\times B$ defined by
\[ (f\times g)(x) = (f(x),g(x)) \]
It returns the pair of observation values. In many cases the combination is ``less abstract'' than the single
functions, because it returns more information about the observed values.
\<close>

subsubsection "Construction Functions"

subsubsection "Wellformedness"

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
