theory Gencot_CArray_Tuples
  imports ShallowShared_Tuples
    Gencot_Default_Tuples
  "HOL-Library.Adhoc_Overloading"
begin

section \<open>Gencot Array Operations\<close>

text \<open>
Gencot array operations are polymorphic on the type of the array elements, the size of the array and
on the type of the index values. 

Although Gencot supports the array operations in Cogent only for Gencot array types (fixed size arrays and 
explicitly sized arrays), it supports them in Isabelle for all other types to which C arrays may
be mapped, such as externally described arrays. We call them generalized array types here.
 
The common property of generalized array types is that the array content is represented in Isabelle 
by a HOL list, optionally together with additional information. For every generalized array type 
two access functions are defined to read and to modify the representing list. Since the additional 
information depends on the specific type of array, no conversion function from list to array can be 
defined for generalized array types in general.

The access functions are polymorphic on the element type and the array size. Then every abstract 
Gencot array operations is defined using the access functions together with a usual operation on 
lists, which is only polymorphic on the list element type but not on the list size. The list size 
restrictions are covered by defining an additional function for specifying the array size, 
polymorphic on the element type. The actual restrictions are not specified here, since they are 
not needed for the refinement proof.

The index values are always assumed to be values of type \<open>'m word\<close> for some bitlength \<open>'m\<close>. So
the polymorphism is reduced on the bitlength \<open>'m\<close>. For actual programs only the bitlengths \<open>8\<close>,
\<open>16\<close>, \<open>32\<close>, and \<open>64\<close> are used, corresponding to the Cogent types U8, U16, U32, U64 used for indexes.

Here the generalized array types are called ``carrays'' and the restricted lists are called ``arrays''.
The carrays are denoted by the type variable \<open>'carr\<close>.
\<close>

subsection \<open>Global Names for Polymorphic Functions\<close>

text \<open>
Polymorphic functions are specified by overloading a global name. If definitions or laws 
shall be available for them, corresponding attributes are defined for collecting them in buckets.

The access functions are \<open>arr\<close> and \<open>arr_update\<close> for retrieving and modifying the representing list.
The size function is \<open>siz\<close>. Attributes are introduced for collecting the definitions of the access
functions and the size function.
\<close>

consts
  arr :: "'carr \<Rightarrow> 'el list"
  arr_update :: "('el list \<Rightarrow> 'el list) \<Rightarrow> 'carr \<Rightarrow> 'carr"
  siz :: "'carr \<Rightarrow> nat"

ML \<open>structure arr_def = Named_Thms (val name = Binding.name "arr_def" val description = "")\<close>
setup \<open> arr_def.setup \<close>
ML \<open>structure arr_update_def = Named_Thms (val name = Binding.name "arr_update_def" val description = "")\<close>
setup \<open> arr_update_def.setup \<close>
ML \<open>structure siz_def = Named_Thms (val name = Binding.name "siz_def" val description = "")\<close>
setup \<open> siz_def.setup \<close>

text \<open>
For the Gencot array operations the global names are declared by the Cogent compiler when it
translates their abstract Cogent declarations. No attributes are introduced for their definitions.
\<close>

text \<open>
For the definition of \<open>modrefArr\<close> pointer referencing / dereferencing functions for the array
elements are required.
These must be overloaded for every type which occurs as element type of an array in a Cogent program.
\<close>

consts
  toPtr :: "'el \<Rightarrow> 'pel"
  frPtr :: "'pel \<Rightarrow> 'el"

subsection \<open>Definitions for the Gencot Array Operations\<close>

text \<open>
The definitions of the polymorphic array operations are specified in a locale. For every 
generalized array type the operation instances are defined by interpreting the locale. The locale
parameters are the access and size functions. The bitlength \<open>'m\<close> of the index type is specified 
by an arbitrary constant of type \<open>'m word\<close>, usually the value \<open>0\<close> can be used for it.\<close>

locale CArrayDefs = 
  fixes arr :: "'carr \<Rightarrow> 'el list"
    and arr_update :: "('el list \<Rightarrow> 'el list) \<Rightarrow> 'carr \<Rightarrow> 'carr"
    and siz :: "'carr \<Rightarrow> nat"
    and idxtypespec :: "('m::len) word"
begin
definition getArr :: "'carr \<times> 'm word \<Rightarrow> 'el"
  where "getArr arg \<equiv> let (c,i) = arg in 
            if unat i \<ge> siz c then hd (arr c) else (nth (arr c) (unat i))"
definition setArr :: "'carr \<times> 'm word \<times> 'el \<Rightarrow> 'carr \<times> unit"
  where "setArr arg \<equiv> let (c,i,e) = arg in 
            (if unat i \<ge> siz c then c else arr_update (\<lambda>a. (list_update a (unat i) e)) c, ())"
definition modifyArr :: "'carr \<times> 'm word \<times> ('el \<times> 'arg \<Rightarrow> 'el \<times> 'out) \<times> 'arg \<Rightarrow> 'carr \<times> 'out"
  where "modifyArr arg \<equiv> 
    let (c, idx, u, inp) = arg;
        i = (if unat idx \<ge> siz c then 0 else unat idx);
        ures = u(nth (arr c) i, inp) 
    in (arr_update (\<lambda>a. (list_update a i (fst ures))) c, snd ures)"
definition modrefArr :: "'carr \<times> 'm word \<times> ('pel \<times> 'arg \<Rightarrow> 'pel \<times> 'out) \<times> 'arg \<Rightarrow> 'carr \<times> 'out"
  where "modrefArr arg \<equiv> 
    let (c, idx, u, inp) = arg; 
        i = (if unat idx \<ge> siz c then 0 else unat idx); 
        ures = u(toPtr (nth (arr c) i), inp)
    in (arr_update (\<lambda>a. (list_update a i (frPtr (fst ures)))) c, snd ures)"
end

subsection \<open>Gencot array types\<close>

text \<open>
The Gencot array types are the types for fixed sized and explicitly sized arrays. They have in common 
that no additional information other than that in the list is represented. Therefore a conversion
function \<open>carr\<close> from list to array can be defined for every Gencot array type.
\<close>

consts carr :: "'el list \<Rightarrow> 'carr"

ML \<open>structure carr_def = Named_Thms (val name = Binding.name "carr_def" val description = "")\<close>
setup \<open> carr_def.setup \<close>

subsubsection \<open>Explicitly sized arrays\<close>

text \<open>
An explicitly sized array is a pair consisting of a list and the explicitly specified size as a 64 bit word.
Indexes always have bitlength \<open>64\<close>. The type \<open>'carr\<close> for an explicitly sized array with elements of type \<open>'el\<close>
is \<open>'el CArrES\<^sub>T\<close>.

The following locale defines the basic array functions.\<close>

locale ESArrBase
begin
definition arr :: "'el CArrES\<^sub>T \<Rightarrow> 'el list" 
  where [arr_def]: "arr \<equiv> fst"
definition arr_update :: "('el list \<Rightarrow> 'el list) \<Rightarrow> 'el CArrES\<^sub>T \<Rightarrow> 'el CArrES\<^sub>T"
  where [arr_update_def]: "arr_update \<equiv> apfst"
definition siz :: "'el CArrES\<^sub>T \<Rightarrow> nat" 
  where [siz_def]: "siz \<equiv> (unat \<circ> snd)"
definition carr :: "'el list \<Rightarrow> 'el CArrES\<^sub>T" 
  where [carr_def]: "carr \<equiv> \<lambda>a. (a,of_nat (length a))"
end

text \<open>
Explicitly sized arrays are introduced by interpreting the following locale and overloading
the defined functions. It extends the basic array functions by the Gencot array 
operations by interpreting \<open>CArrayDefs\<close> as sublocale.
\<close>
locale ESArrDefs = ESArrBase
begin
sublocale CArrayDefs arr arr_update siz "0::64 word" .
end

subsubsection \<open>Fixed sized arrays\<close>

text \<open>
For fixed sized arrays there is a type for every size used in the Cogent program.
In addition to the normal Gencot array operations Gencot defines polymorphic conversion
functions from and to explicitly sized arrays. The following locale takes the size value
as parameter instead of the size function. It defines the size function and it defines
\<open>arr_update\<close> from the conversion function \<open>carr\<close>. Then it
specifies definitions for the conversion functions from/to explicitly sized arrays. 
\<close>

locale FxdArrBase = 
  fixes arr :: "'carr \<Rightarrow> 'el list"
    and carr :: "'el list \<Rightarrow> 'carr"
    and fxdsiz :: "nat"
begin

definition siz :: "'carr \<Rightarrow> nat"
  where fxdsiz_def[siz_def]: "siz c \<equiv> fxdsiz"
definition arr_update :: "('el list \<Rightarrow> 'el list) \<Rightarrow> 'carr \<Rightarrow> 'carr"
  where [arr_update_def]: "arr_update u \<equiv> carr \<circ> u \<circ> arr"

definition toCAES :: "'carr \<Rightarrow> 'el CArrES\<^sub>T"
  where "toCAES a \<equiv> (arr a, of_nat (fxdsiz))"
definition fromCAES :: "'el CArrES\<^sub>T \<Rightarrow> 'carr"
  where "fromCAES aes \<equiv> carr (fst aes)"
definition rotoCAES :: "'carr \<Rightarrow> 'el CArrES\<^sub>T"
  where [simp]: "rotoCAES a \<equiv> toCAES a"
definition rofromCAES :: "'el CArrES\<^sub>T \<Rightarrow> 'carr"
  where [simp]: "rofromCAES aes \<equiv> fromCAES aes"

end

text \<open>
The following locale extends \<open>FxdArrBase\<close> and provides 
the definitions of the normal Gencot array operations by interpreting \<open>CArrayDefs\<close>.

It is intended to be interpreted once for every size of fixed carrays occurring in the C program,
together with a specification for the bitlength of the index values. These interpretations only 
provide the definitions of the Gencot array operations which is sufficient for the refinement
proof.
\<close>

locale FxdArrDefs = FxdArrBase arr carr fxdsiz
  for arr :: "'carr \<Rightarrow> 'el list"
  and carr :: "'el list \<Rightarrow> 'carr"
  and fxdsiz :: "nat"
+ 
fixes idxtypespec :: "('m::len) word"
begin
sublocale CArrayDefs arr arr_update siz idxtypespec .
end

end
