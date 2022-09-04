theory Gencot_CArray_Semantics
  imports "Gencot_CArray_Tuples"
  "Gencot_SemanticsSupport"
begin

section \<open>Support for Reasoning with Array Types\<close>

text \<open>
Array types include the predefined Gencot array types for fixed arrays and for explicitly sized 
arrays, and all user defined types which behave like arrays (generalized array types).
All these types have in common, that they have a nonempty list as a part for representing
the array and that an explicit size function exists for the array. 

The actual reasoning support is defined for lists in theory \<open>Gencot_ArraySupport\<close>
\<close>

subsection \<open>Basic Reasoning Support for all Array Types\<close>

subsubsection \<open>Wellsizedness\<close>

text \<open>
Support for restricting the array size is provided by a separate size function \<open>siz\<close>
and a wellsizedness predicate \<open>wlsd\<close> which states that the length of the representing
list is the same as the value of the size function and is not \<open>0\<close>. The function \<open>siz\<close> is the same as 
the size function introduced in \<open>Gencot_CArray_Tuples\<close> for the Gencot array types.

The predicate \<open>wlsd\<close> is defined generically as \<open>wlsdGen\<close>, depending on the functions \<open>arr\<close> and \<open>siz\<close>.
By adhoc overloading the constant \<open>wlsd\<close> with instances of \<open>wlsdGen\<close> for actual instances of 
\<open>arr\<close> and \<open>siz\<close> the predicate can always be specified as \<open>wlsd\<close>. Applications can be unfolded by
using the definition of \<open>wlsdGen\<close> which is renamed to \<open>wlsd_def\<close>.
\<close>

consts wlsd :: "'carr \<Rightarrow> bool"

definition wlsdGen :: "('carr \<Rightarrow> 'el list) \<Rightarrow> ('carr \<Rightarrow> nat) \<Rightarrow> 'carr \<Rightarrow> bool"
  where wlsd_def: "wlsdGen a s c \<equiv> s c = length (a c) \<and> s c > 0"

text \<open>
All array modification functions should preserve wellsizedness. The predicate
\<open>prsvp\<close> is combined with \<open>wlsd\<close> instances to express this property. 

The lemma bucket \<open>wlsd\<close> is introduced for collecting wellsizedness propositions 
about arrays, array construction functions and array modification functions.
\<close>

ML \<open>structure wlsd = Named_Thms (val name = Binding.name "wlsd" val description = "")\<close>
setup \<open> wlsd.setup \<close>

text \<open>
The basic laws are defined using the locale \<open>Wlsd\<close>, so that they can easily be introduced
for other wellsizedness predicates.
\<close>

locale Wlsd =
  fixes wls :: "'x \<Rightarrow> bool"
begin
lemma prsvwlsd_const[wlsd]: "wls x \<Longrightarrow> prsvp wls (\<lambda>_.x)"
  by(simp add: prsvp_def)
lemma prsvwlsd_id[wlsd]: "prsvp wls (\<lambda>a. a)"
  by(simp add: prsvp_def)
end

subsubsection \<open>Wellsizedness Preservation\<close>

text \<open>
The combination of \<open>prsvp\<close> and \<open>wlsdGen\<close> is abbreviated as \<open>prsvwlsdGen\<close>.
By adhoc overloading the constant \<open>prsvwlsd\<close> with instances of \<open>prsvwlsdGen\<close> for actual instances of 
\<open>arr\<close> and \<open>siz\<close> the predicate can be specified as \<open>prsvwlsd\<close> for all arrays. 
Applications can be unfolded by using the definition of \<open>prsvp\<close>.

The rules for inferring \<open>prsvwlsd\<close> and \<open>wlsd\<close> properties for function and function
application terms could be specified generically for all functions. However, for
complex terms unification for such rules not always works. Therefore the locale
\<open>Prsvwlsd\<close> is introduced which generates specific rules for every modification 
function when interpreted for the function.
\<close>

consts 
  prsvwlsd :: "('carr \<Rightarrow> 'carr) \<Rightarrow> bool"

abbreviation "prsvwlsdGen a s \<equiv> prsvp (wlsdGen a s)"

locale Prsvwlsd =
  fixes wls :: "'x \<Rightarrow> bool"
    and upd :: "'x \<Rightarrow> 'x"
begin
lemma wlsdRule[wlsd]:
 "\<lbrakk>wls x; prsvp wls upd\<rbrakk> \<Longrightarrow> wls (upd x)"
  by(simp add: prsvp_def)
lemma prsvwlsd_comp[wlsd]:
 "\<lbrakk>prsvp wls u; prsvp wls upd\<rbrakk> \<Longrightarrow> prsvp wls (upd \<circ> u)"
  by(simp add: prsvp_def)
lemma prsvwlsd_appl[wlsd]:
 "\<lbrakk>prsvp wls u; prsvp wls upd\<rbrakk> \<Longrightarrow> prsvp wls (\<lambda>x. upd (u x))" 
  by(simp add: prsvp_def)
lemmas rules = wlsdRule prsvwlsd_comp prsvwlsd_appl
end

text \<open>
The following locales combine \<open>Prsvwlsd\<close> with common cases for wellsizedness
preservation of modification functions
\<close>

text \<open>
Case: a modification function \<open>upd\<close> is always wellsized.
\<close>
locale PrsvwlsdAlways = P: Prsvwlsd wls upd
  for wls and upd
  +
assumes prsvwlsd[wlsd]: "prsvp wls upd"
begin
lemmas rules = prsvwlsd P.rules
end

text \<open>
Case: a modification function \<open>upd\<close> takes a part modification function \<open>updprt\<close> as argument
and is wellsized \<open>wls\<close> for the whole, if \<open>updprt\<close> is wellsized \<open>wlsprt\<close> for the part.
\<close>
locale PrsvwlsdIfpart = P: Prsvwlsd wls "upd updprt"
  for wls and upd::"('x, 'y) PartUpdate" and updprt
  +
  fixes wlsprt :: "'y \<Rightarrow> bool"
assumes prsvwlsd[wlsd]: "prsvp wlsprt updprt \<Longrightarrow> prsvp wls (upd updprt)"
begin
lemmas rules = prsvwlsd P.rules
end

text \<open>
Case: a modification function \<open>upd\<close> takes a part modification function \<open>updlst\<close> for a list
as argument and the list elements may contain nested arrays. Function \<open>upd\<close> is
wellsized \<open>wls\<close> for the whole, if \<open>updlst\<close> preserves the list length and
the nested wellsized predicate \<open>wlselm\<close> for all list elements. 

If there are no nested arrays in the elements, use \<open>\<top>\<close> for \<open>wlselm\<close>.
\<close>
locale PrsvwlsdIfarr = P: Prsvwlsd wls "upd updlst"
  for wls and upd::"('x, 'el list) PartUpdate" and updlst
  +
fixes wlselm :: "'el \<Rightarrow> bool"
assumes prsvwlsd[wlsd]: "\<lbrakk>prsvlen updlst; prsvelmsp wlselm updlst\<rbrakk> \<Longrightarrow> prsvp wls (upd updlst)"
begin
lemmas rules = prsvwlsd P.rules
end

subsubsection \<open>Wellsizedness for Nested Arrays\<close>

text \<open>
For nested arrays all elements of the outer array must satisfy wellsizedness
for all inner arrays. For every actual outer array this can be expressed by
combining \<open>wlsd\<close> with \<open>elmsp wlsdelm\<close> where \<open>wlsdelm\<close> is a predicate for 
the wellsizedness of all nested arrays in an element. No separate predicate 
should be defined for the combination of \<open>wlsd\<close> with \<open>elmsp wlsdelm\<close> because that
would require additional laws which result in cycles for the simplifier. Instead,
use an abbreviation to introduce a name for the combination.

In a similar way as \<open>wlsd\<close> and \<open>prsvwlsd\<close> the predicates \<open>arrp\<close> and \<open>prsvarrp\<close>
are defined to lift \<open>elmsp\<close> and \<open>prsvelmsp\<close> from lists to arrays. The corresponding rules
are generated by locale \<open>Prsvarrp\<close> and collected in the \<open>lstp\<close> bucket.
\<close>

consts 
  arrp :: "('el \<Rightarrow> bool) \<Rightarrow> 'carr \<Rightarrow> bool"
  prsvarrp :: "('el \<Rightarrow> bool) \<Rightarrow> ('carr \<Rightarrow> 'carr) \<Rightarrow> bool"

definition arrpGen :: "('carr \<Rightarrow> 'el list) \<Rightarrow> ('el \<Rightarrow> bool) \<Rightarrow> 'carr \<Rightarrow> bool"
  where arrp_def: "arrpGen a p c \<equiv> elmsp p (a c)"
definition prsvarrpGen :: "('carr \<Rightarrow> 'el list) \<Rightarrow> ('el \<Rightarrow> bool) \<Rightarrow> ('carr \<Rightarrow> 'carr) \<Rightarrow> bool"
  where prsvarrp_def: "prsvarrpGen a p u \<equiv> \<forall>x. arrpGen a p x \<longrightarrow> arrpGen a p (u x)"

lemma prsvarrp[lstp]: "prsvarrpGen a p f \<Longrightarrow> prsvp (arrpGen a p) f"
  by(simp add: prsvarrp_def prsvp_def)
lemma prsvarrp_const[lstp]: "arrpGen a p x \<Longrightarrow> prsvarrpGen a p (\<lambda>_.x)"
  by(simp add: prsvarrp_def)
lemma prsvarrp_id[lstp]: "prsvarrpGen a p (\<lambda>a. a)"
  by(simp add: prsvarrp_def)

locale Prsvarrp =
  fixes arr :: "'carr \<Rightarrow> 'el list"
    and upd :: "'carr \<Rightarrow> 'carr"
begin
lemma arrpRule[lstp]:
 "\<lbrakk>arrpGen arr p x; prsvarrpGen arr p upd\<rbrakk> \<Longrightarrow> arrpGen arr p (upd x)"
  by(simp add: arrp_def prsvarrp_def)
lemma prsvarrp_comp[lstp]:
 "\<lbrakk>prsvarrpGen arr p upd; prsvarrpGen arr p u\<rbrakk> \<Longrightarrow> prsvarrpGen arr p (upd \<circ> u)"
  by(simp add: arrp_def prsvarrp_def)
lemma prsvarrp_appl[lstp]:
 "\<lbrakk>prsvarrpGen arr p upd; prsvarrpGen arr p u\<rbrakk> \<Longrightarrow> prsvarrpGen arr p (\<lambda>x. upd (u x))" 
  by(simp add: arrp_def prsvarrp_def)
lemmas rules = arrpRule prsvarrp_comp prsvarrp_appl
end

subsubsection \<open>Locale with Basic Rules for all Array Types\<close>

text \<open>
This is an extension of the part access rules for the access functions \<open>arr\<close> and \<open>arr_update\<close>
for the representing list.
\<close>

locale CArrayRules = PartAccess arr arr_update
  for arr :: "'carr \<Rightarrow> 'el list"
  and arr_update :: "('carr, 'el list) PartUpdate"
+
fixes siz :: "'carr \<Rightarrow> nat" 
assumes prsvwlsd_arr_update[wlsd]: 
            "prsvlen u \<Longrightarrow> prsvp (wlsdGen arr siz) (arr_update u)"
begin

text \<open>
Introduce shortcut sameUpd rules for the composition \<open>elm \<circ> arr\<close>, since the sameUpd rules
for the single functions do not compose directly.
\<close>
lemma elmarr_sameUpdRule[sameUpd]: 
  "arr_update (elm_update i (\<lambda>_. u (elm i (arr a)))) a = arr_update (elm_update i u) a"
  apply(subst local.sameUpdRule[symmetric])
  apply(subst ElmAccess.sameUpdRule)
  by(simp add: sameUpd)
lemma elmarr_idsameUpdRule[simp]: 
  "arr_update (elm_update i (\<lambda>_. (elm i (arr a)))) a = a"
  apply(subst id_apply[where x="(elm i (arr a))",symmetric])
  by(subst elmarr_sameUpdRule,simp add: id_def)

text \<open>
Wellsizedness and wellszedness preservation for \<open>arr_update\<close>.
\<close>
adhoc_overloading 
      wlsd     "wlsdGen arr siz"
  and prsvarrp "prsvarrpGen arr"

sublocale Wlsd "wlsd" .

sublocale Prsvwlsd_arr_update: Prsvwlsd "wlsd" "arr_update u" for u .

lemma prsvarrp_arr_update[lstp]:
 "prsvelmsp p u \<Longrightarrow> prsvarrp p (arr_update u)"
  by(simp add: prsvarrp_def prsvp_def arrp_def)
sublocale Prsvarrp_arr_update: Prsvarrp arr "arr_update u" for u .

end

subsection "Semantics for the Gencot Array Operations"

text \<open>
For all Gencot array operations, semantics theorems are provided for the normal case and the
error case, in which the index is invalid.

The following locale extends \<open>CArrayRules\<close> by the definitions from \<open>CArrayDefs\<close> and
provides the semantics theorems.
\<close>

locale CArray = CArrayRules arr arr_update siz
  for arr :: "'carr \<Rightarrow> 'el list"
  and arr_update :: "('carr, 'el list) PartUpdate"
  and siz :: "'carr \<Rightarrow> nat" 
+
fixes idxtypespec :: "('m::len) word"
begin

sublocale CArrayDefs arr arr_update siz idxtypespec .

text \<open>
The Gencot array operations are defined using the explicit size.
The semantics theorems assume wellsizedness to relate this to the length of the representing list.
An invalid index is considered as error, for every function a regular semantics is specified
as well as an error semantics. The semantics theorems are added to the sem bucket.
The error semantics are collected in \<open>errsem_C\<close>.
\<close>

definition error_getArr :: "'carr \<times> 'm word \<Rightarrow> bool"
  where [simp]:
  "error_getArr x \<equiv> let (a,i) = x in \<not> vld (arr a) (unat i)"
theorem sem_getArr[sem]: 
 "\<lbrakk>wlsd a; \<not> error_getArr (a,i)\<rbrakk> \<Longrightarrow> 
  getArr (a,i) = elm (unat i) (arr a)"
  by (simp add: getArr_def elm wlsd_def)
theorem errsem_getArr:
 "\<lbrakk>wlsd a; error_getArr (a,i)\<rbrakk> \<Longrightarrow> 
  getArr (a,i) = elm 0 (arr a)"
  by(auto simp add: getArr_def elm wlsd_def hd_conv_nth)

definition error_setArr :: "'carr \<times> 'm word \<times> 'el \<Rightarrow> bool"
  where [simp]:
  "error_setArr x \<equiv> let (a,i,v) = x in \<not> vld (arr a) (unat i)"
theorem sem_setArr[sem]: 
 "\<lbrakk>wlsd (fst x); \<not> error_setArr x\<rbrakk> \<Longrightarrow> 
  setArr x = (let (a,i,v) = x in (arr_update (elm_update (unat i) (\<lambda>_.v)) a, ()))"
  apply (auto simp add: setArr_def wlsd_def)
  by (auto simp add: wlsd_def elm_update prsvlen_def)
theorem errsem_setArr:
 "\<lbrakk>wlsd (fst x); error_setArr x\<rbrakk> \<Longrightarrow> 
  setArr x = ((fst x),())"
  by (simp add: setArr_def split_def wlsd_def)
definition error_modifyArr :: "'carr \<times> 'm word \<times> ('el \<times> 'arg \<Rightarrow> 'el \<times> 'out) \<times> 'arg \<Rightarrow> bool"
  where [simp]:
  "error_modifyArr x \<equiv> let (a,(i,_)) = x in \<not> vld (arr a) (unat i)"
theorem sem_modifyArr[sem]:
 "\<lbrakk>wlsd (fst x); \<not> error_modifyArr x\<rbrakk> \<Longrightarrow> 
  modifyArr x = 
  (let (a,(i,f,x)) = x; (e,y) = f (elm (unat i) (arr a), x) in (arr_update (elm_update (unat i) (\<lambda>_.e)) a, y))"
  by (auto simp add: modifyArr_def split_def Let_def elm_update elm wlsd_def prsvlen_def)
theorem errsem_modifyArr:
 "\<lbrakk>wlsd (fst x); error_modifyArr x\<rbrakk> \<Longrightarrow> 
  modifyArr x = (let (a,(_,f,x)) = x in modifyArr (a,(0,f,x)))"
  by (simp add: modifyArr_def split_def Let_def wlsd_def)
definition error_modrefArr :: "'carr \<times> 'm word \<times> ('pel \<times> 'arg \<Rightarrow> 'pel \<times> 'out) \<times> 'arg \<Rightarrow> bool"
  where [simp]:
  "error_modrefArr x \<equiv> let (a,(i,f,v)) = x in \<not> vld (arr a) (unat i)"
theorem sem_modrefArr[sem]:
 "\<lbrakk>wlsd (fst x); \<not> error_modrefArr x\<rbrakk> \<Longrightarrow> 
  modrefArr x = 
  (let (a,(i,f,x)) = x; (e,y) = f (toPtr (elm (unat i) (arr a)), x) in (arr_update (elm_update (unat i) (\<lambda>_.frPtr e)) a, y))"
  by (auto simp add: modrefArr_def split_def Let_def elm_update elm wlsd_def prsvlen_def)
theorem errsem_modrefArr:
 "\<lbrakk>wlsd (fst x); error_modrefArr x\<rbrakk> \<Longrightarrow> 
  modrefArr x = (let (a,(i,f,x)) = x in modrefArr (a,(0,f,x)))"
  by (simp add: modrefArr_def split_def Let_def wlsd_def)

lemmas sem_C =
  sem_getArr sem_setArr sem_modifyArr sem_modrefArr
lemmas errsem_C = 
  errsem_getArr errsem_setArr errsem_modifyArr errsem_modrefArr
end

subsection "Explicitly Sized Arrays"

text \<open>
The basic functions are defined by interpreting \<open>ESArrBase\<close>. 
\<close>

interpretation ESA: ESArrBase .
adhoc_overloading
      arr ESA.arr
  and siz ESA.siz
  and arr_update ESA.arr_update
  and carr ESA.carr

text \<open>
The basic support and Gencot array operation semantics is provided
by interpreting \<open>CArray\<close>.
\<close>

interpretation ESArray: CArray ESA.arr ESA.arr_update ESA.siz "0::64 word"
  apply(unfold_locales,unfold arr_update_def)
      by(auto simp add: arr_def carr_def siz_def prsvlen_def prsvp_def wlsd_def)

adhoc_overloading 
      wlsd       "wlsdGen ESA.arr ESA.siz" 
  and arrp       "arrpGen ESA.arr"
  and prsvwlsd   "prsvwlsdGen ESA.arr ESA.siz"
  and prsvarrp   "prsvarrpGen ESA.arr"
  and getArr ESArray.getArr
  and setArr ESArray.setArr
  and modifyArr ESArray.modifyArr
  and modrefArr ESArray.modrefArr

lemmas wlsdRulesES = 
  ESArray.prsvwlsd_arr_update ESArray.Prsvwlsd_arr_update.rules
lemmas arrpRulesES = 
  ESArray.prsvarrp_arr_update ESArray.Prsvarrp_arr_update.rules 

text \<open>
Wellsizedness implications about the list length  are added to the simpset.
They are intended to be applied backwards by the simplifier. To cover most cases
they are specified in two variants.
\<close>

lemma wlsdES_implies_length[simp]: 
  "wlsd (a,s) \<Longrightarrow> length a = unat s"
  "wlsd esa \<Longrightarrow> length (fst esa) = unat (snd esa)"
  by(unfold wlsd_def,simp_all add: arr_def siz_def)

lemma wlsdES_implies_notempty[simp]: 
  "wlsd (a,s) \<Longrightarrow> a \<noteq> []"
  "wlsd esa \<Longrightarrow> (fst esa) \<noteq> []"
  by(unfold wlsd_def,auto simp add: arr_def siz_def)

text \<open>
Due to the representation of the size as a 64 bit word, wellsizedness implies that the 
list size is restricted.
\<close>
lemma wlsdES_implies_lenless[simp]: 
  "wlsd (a,s) \<Longrightarrow> length a < 2^64"
  "wlsd esa \<Longrightarrow> length (fst esa) < 2^64"
  apply(unfold wlsd_def,simp_all add: arr_def siz_def)
  by(unat_arith,simp,unat_arith,simp)

text \<open>
If the function \<open>arr\<close> is explicitly specified in a term, it must be eliminated
to apply the rules above. This is done by the simplifier only in the context of \<open>length\<close>,
because in general the function \<open>arr\<close> may be needed to apply other rules. Then it may
be eliminated by explicitly unfolding \<open>arr_def\<close>. 
\<close>
lemma length_arrES[simp]: "length (arr (a,s)) = length a"
  by(simp add: arr_def)

text \<open>
The following rule is also a wellsizedness implication about the list length, 
it can be used to eliminate \<open>carr\<close> for explicitly sized arrays instead of \<open>carr_def\<close>.
It is not applied automatically by the simplifier because that would prevent 
alternatives. 
\<close>
lemma wlsdES_carr: "wlsd (a,s) \<Longrightarrow> carr a = (a,s)"
  apply(unfold wlsd_def,clarsimp simp add: siz_def carr_def arr_def)
  apply(drule_tac f=of_nat in arg_cong) 
  by(subst (asm) word_unat.Rep_inverse,simp)

text \<open>
The \<open>arrp\<close> predicate only depends on the representing list, therefore it is automatically
simplified for explicitly sized arrays which are constructed only from the list.
\<close>

lemma arrpES_elmsp[simp]: "arrp p (carr a) = elmsp p a"
  by(unfold arrp_def,simp add: arr_def carr_def)

text \<open>
If an explicitly sized array is constructed in a function, also wellsizedness assumption
and possibly \<open>arrp\<close> assumptions must be constructed. 
The following rules are defined for that purpose, they are intended to be
applied with method drule or frule. 
\<close>
(* this will create subgolas of the form LENGTH(32) \<le> 64 *)
(* they can be solved by apply(subgoal_tac "LENGTH(32) = 32",simp,simp) *)
(* but there should be a nicer way? *)
lemma wlsdES_dest: "\<lbrakk>unat s = x; x = length a; a \<noteq>[]; LENGTH('b) \<le> 64\<rbrakk> \<Longrightarrow> wlsd (a,ucast s)" for s::"'b::len word"
  by(unfold wlsd_def,simp add: siz_def arr_def)

lemma arrpES_dest: "elmsp p a \<Longrightarrow> arrp p (a,s)"
  by(unfold arrp_def,simp add: arr_def carr_def)

subsection \<open>Fixed Sized Arrays\<close>

text \<open>
For fixed sized arrays the constructor function \<open>mkFxdArr\<close> is defined which need no
specification of the array size. It takes as argument a function for filling in the elements, 
depending on their index.
\<close>

consts mkFxdArr :: "(nat \<Rightarrow> 'el) \<Rightarrow> 'carr"

text \<open>
The following locale extends \<open>FxdArrBase\<close>, defines \<open>mkFxdArr\<close>, and provides the basic support and 
Gencot array operation semantics by interpreting \<open>CArray\<close> and provides wellsizedness rules. 

Additionally it provides  semantics
theorems for \<open>toCAES\<close> and \<open>fromCAES\<close> and transfer lemmas for \<open>arr\<close>, \<open>arr_update\<close>, \<open>siz\<close>, 
and \<open>wlsd\<close>. It also provides transfer lemmas for \<open>arr\<close>, \<open>arr_update\<close>, \<open>siz\<close>, and \<open>wlsd\<close> with 
respect to \<open>mkFxdArr\<close>, they require the assumption \<open>fxdsiz > 0\<close>.
\<close>

locale FxdArr = FxdArrBase arr carr fxdsiz
  for arr :: "'carr \<Rightarrow> 'el list"
  and carr :: "'el list \<Rightarrow> 'carr"
  and fxdsiz :: "nat"
  +
  fixes idxtypespec :: "('m::len) word"
  assumes arr_inverse: "\<And>x. carr (arr x) = x" 
      and carr_inverse: "\<And>x. arr (carr x) = x"
      and notempty: "fxdsiz > 0"
begin

definition mkFxdArr :: "(nat \<Rightarrow> 'el) \<Rightarrow> 'carr"
  where "mkFxdArr f \<equiv> carr [f i. i \<leftarrow> [0..< fxdsiz]]"

adhoc_overloading 
      wlsd     "wlsdGen arr siz" 
  and arrp     "arrpGen arr"
  and prsvwlsd "prsvwlsdGen arr siz"
  (* wlsd and prsvwlsd must be overloaded here because they depend on the specific siz from FxdArrBase *)
  (* prsvarrp must not be overloaded because it depends on the common arr and carr
     and is already overloaded in CArrayBase *)
  (* arrp also depends on the common arr and carr, but is not overloaded in CArrayBase *)

sublocale CArray arr arr_update siz idxtypespec
  apply(unfold_locales)
        apply(auto simp add: arr_def arr_update_def carr_inverse arr_inverse prsvp_def prsvlen_def)
  by(unfold wlsd_def,auto simp add: FxdArrBase.fxdsiz_def carr_inverse)

text \<open>
Wellsizedness implications are added to the simpset. The first rule reduces list length
to the fixed size value, the second rule derives that the list is not empty.
\<close>
lemma wlsd_implies_length[simp]: "wlsd a \<Longrightarrow> length (arr a) = fxdsiz"
  by(unfold wlsd_def,simp add: siz_def)
lemma wlsd_implies_notempty[simp]: "wlsd a \<Longrightarrow> (arr a) \<noteq> []"
  by(unfold wlsd_def,auto)

text \<open>
The \<open>mkFxdArr\<close> function always creates wellsized arrays.
\<close>
lemma allwlsd_mk[wlsd]:
 "wlsd (mkFxdArr f)"
  by(simp add: mkFxdArr_def wlsd_def siz_def carr_inverse notempty)

lemma allarrp_mk[lstp]:
 "\<forall>i. p (f i) \<Longrightarrow> arrp p (mkFxdArr f)"
  by(simp add: mkFxdArr_def arrp_def carr_inverse elmsp_def)

lemmas wlsdRules = 
  prsvwlsd_arr_update Prsvwlsd_arr_update.rules
  allwlsd_mk 
lemmas arrpRules = 
  prsvarrp_arr_update Prsvarrp_arr_update.rules
  allarrp_mk 

text \<open>Semantics of Cogent array conversion functions.\<close>

theorem sem_toCAES[sem]:
 "wlsd a \<Longrightarrow> toCAES a = (arr a, of_nat (length (arr a)))"
  by(unfold wlsd_def,simp add: FxdArrBase.toCAES_def siz_def)
theorem sem_fromCAES[sem]:
 "wlsd aes \<Longrightarrow> 
  fromCAES aes = carr (ESA.arr aes)"
  by(simp add: fromCAES_def arr_def)

text \<open>
Transfer lemmas for the Cogent array conversion functions.
\<close>

lemma wlsdToCAES: 
 "wlsd a \<and> siz a < 2^64 \<Longrightarrow> 
  wlsd (toCAES a)"
  apply(simp add: sem_toCAES) 
  by(unfold wlsd_def,auto simp add: siz_def arr_def unat_of_nat)
lemma wlsdFromCAES: 
 "wlsd aes \<and> ESA.siz aes = fxdsiz \<Longrightarrow> 
  wlsd (fromCAES aes)"
  by(unfold wlsd_def,simp add: fromCAES_def siz_def arr_def carr_inverse)

lemma sizToCAES[simp]: 
 "siz a < 2^64 \<Longrightarrow> 
  ESA.siz (toCAES a) = siz a"
  by(simp add: toCAES_def siz_def unat_of_nat)
lemma sizFromCAES[simp]: 
 "ESA.siz aes = fxdsiz \<Longrightarrow> 
  siz (fromCAES aes) = ESA.siz aes"
  by(simp add: fromCAES_def siz_def)

lemma arrToCAES:
 "ESA.arr (toCAES a) = arr a"
  by(simp add: toCAES_def arr_def)
lemma arrFromCAES:
 "arr (fromCAES aes) = ESA.arr aes"
  by(simp add: fromCAES_def arr_def carr_inverse)

lemma arr_updateToCAES:
 "ESA.arr_update u (toCAES a) = toCAES (arr_update u a)"
  by(simp add: toCAES_def ESA.arr_update_def arr_update_def arr_def siz_def carr_inverse)
lemma arr_updateFromCAES:
 "arr_update u (fromCAES aes) = fromCAES (ESA.arr_update u aes)"
  by(simp add: fromCAES_def ESA.arr_update_def arr_update_def arr_def siz_def carr_inverse)

lemmas transCAES = wlsdToCAES wlsdFromCAES sizToCAES sizFromCAES arrToCAES arrFromCAES arr_updateToCAES arr_updateFromCAES

text \<open>
Transfer lemmas for \<open>mkFxdArr\<close>.
\<close>

lemma sizMk:
 "siz (mkFxdArr f) = fxdsiz"
  by(simp add: mkFxdArr_def siz_def)

lemma arrMk:
 "arr (mkFxdArr f) = [f i. i \<leftarrow> [0..< fxdsiz]]"
  by(simp add: mkFxdArr_def carr_inverse)

lemma arr_updateMk:
 "arr_update u (mkFxdArr f) = carr (u [f i. i \<leftarrow> [0..< fxdsiz]])"
  by (simp add: mkFxdArr_def arr_update_def carr_inverse)

lemmas transMk = sizMk arrMk arr_updateMk

text \<open>
Useful lemma for the common case of initializing an array with a constant value.
\<close>

lemma constMk:
 "mkFxdArr (\<lambda>_. v) = carr (replicate fxdsiz v)"
  by(auto simp add: mkFxdArr_def map_replicate_const)

end

subsection \<open>Named Array Sizes\<close>

text \<open>
If the size of a fixed array is specified by a named constant in C and Cogent, a corresponding
named constant is present in the shallow embedding and can be used to specify the array size
independently of the actual value. This is done by using the named constant as \<open>fxdsiz\<close> in the
\<open>FxdArr\<close> interpretation.

Since the named constant generated by Cogent has a word type, it must be converted to type
\<open>nat\<close> to be used as \<open>fxdsiz\<close>. This can be done by introducing a second named constant for the
\<open>nat\<close> value. 

This way the named constant becomes a part of the specific \<open>siz\<close> function term introduced by the 
\<open>FxdArr\<close> interpretation, and thus also of the corresponding instances of \<open>wlsd\<close> and \<open>prsvwlsd\<close>
and all rules for them. If the named constant is unfolded to its value in a term, all these rules 
do not apply anymore for the term.

The following locale can be used to generate rules which are typically needed for reasoning about
array indexes. The rules cover those cases where the value of the named constant is relevant.
These rules are added to the simpset, so they are automatically applied without the need to
unfold the named constant.

Additionally a rule \<open>to_C\<close> is generated which can be used to convert the value to the named 
constant. This is required because Cogent unfolds the named constants whenever it inserts it
into the shallow embedding code. The rule must be processed by simplifying the left hand side
and unfolding \<open>cogent_C\<close>, so that a literal value of type \<open>'n word\<close> results.

The locale takes as parameters the named constant of type \<open>'m word\<close>, the corresponding named 
constant of type \<open>nat\<close>, and the type \<open>'n word\<close> to be used for the array index values. All values
which are lower than the named constant must be representable by this type. The \<open>unat_of_nat\<close>
assumption can be proved using the global \<open>unat_of_nat\<close> rule and unfolding the named constant.
\<close>

locale NamedSizeRules = 
  fixes cogent_C :: "('m::len) word"
    and nat_C :: nat
    and wordtypespec :: "('n::len) word"
  assumes rel_C: "nat_C = unat cogent_C"
    and nat_C: "nat_C < 2^LENGTH('n)"
begin 
lemma unat_of_nat[simp]: "i \<le> nat_C \<Longrightarrow> (unat ((of_nat i):: 'n word)) = i"
  apply(insert nat_C)
  by(simp add: unat_of_nat)
lemma to_C:
  "(of_nat (unat cogent_C)) = ((of_nat nat_C)::'n word)" 
  by (simp add: rel_C)
lemma less_nat_implies_less_word[simp]: "i < nat_C \<Longrightarrow> ((of_nat i):: 'n word) < of_nat nat_C"
  by(simp add: word_less_nat_alt)
lemma less_nat_implies_neq_word[simp]: "i < nat_C \<Longrightarrow> ((of_nat i):: 'n word) \<noteq> of_nat nat_C"
  by(simp add: word_less_nat_alt less_imp_neq)
lemma less_nat_iff_less_word[simp]: "(unat (i:: 'n word) < nat_C) \<Longrightarrow> (i < of_nat nat_C)" 
  by(simp add: word_less_nat_alt)
lemma unat_add[simp]: "unat (n::'n word) + i < nat_C \<Longrightarrow> unat (n + of_nat i) = unat n + i"
  apply(insert nat_C)
  by(simp add: unat_word_ariths)
end

end
