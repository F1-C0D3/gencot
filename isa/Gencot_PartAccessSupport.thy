section \<open>Part Access Support\<close>

theory Gencot_PartAccessSupport
  imports Gencot_PreservationSupport
begin

text \<open>
This theory introduces reasoning support for access functions for parts of data structures.
It is a generalization and extension for the support of record types where the parts are 
the fields. Data structures may be nested records and arrays or more abstract entities
which have parts.

For every part it is assumed that there are two access functions: an observation function 
\<open>prt\<close> which returns the part and an update function \<open>prt_update\<close> which applies a 
modification function to the part. Parts are always disjunct, an update of one part 
does not affect other parts.

The theory provides laws for single parts, for pairs of parts, and for whole data structures.
Since the number of parts may be large for certain structures, and the number of part
pair laws is quadratic in the number of parts, the generic support here is defined in a 
way that it can be applied to isolated parts and part pairs as well as to small structures
as a whole. 

The support is provided in the form of locales which can be interpreted for actual structures
and their parts to introduce corresponding laws with a common naming scheme. Some laws are 
automatically collected in buckets or added to the simpset. Whenever possible the laws are 
provided in an applicative form and a composition form so that they can be easily used for
both situations. The applicative form is used as locale assumption, since it is usually easier
to prove, the composition form is derived from it as a lemma in the locale.
\<close>

type_synonym ('whol, 'part) PartUpdate = "('part \<Rightarrow> 'part) \<Rightarrow> 'whol \<Rightarrow> 'whol"

text\<open>
Define lemma buckets which collect certain laws for all structures and all their parts.
\<close>

ML \<open>structure sameUpd = Named_Thms (val name = Binding.name "sameUpd" val description = "")\<close>
setup \<open> sameUpd.setup \<close>
ML \<open>structure distUpd = Named_Thms (val name = Binding.name "distUpd" val description = "")\<close>
setup \<open> distUpd.setup \<close>
ML \<open>structure commUpd = Named_Thms (val name = Binding.name "commUpd" val description = "")\<close>
setup \<open> commUpd.setup \<close>
ML \<open>structure allUpd = Named_Thms (val name = Binding.name "allUpd" val description = "")\<close>
setup \<open> allUpd.setup \<close>

subsection \<open>Laws for a Single Part\<close>

text \<open>
The following locale defines the functor laws for a part update function. They make 
the structure be a functor with the update function being the mapping function for the 
part.
\<close>
locale PartUpdate = 
  fixes prt_update :: "('whol, 'part) PartUpdate"
  assumes distUpdApp[distUpd]: "prt_update u1 (prt_update u2 x) = prt_update (u1 \<circ> u2) x"
      and identUpdRule[simp]: "prt_update (\<lambda>a. a) = (\<lambda>a. a)"
begin
lemma distUpdComp[distUpd]: "(prt_update u1) \<circ> (prt_update u2) = prt_update (u1 \<circ> u2)"
  by(rule ext,simp add: distUpdApp)
end 

text \<open>
The following locales extend \<open>PartUpdate\<close> by laws for relating an observation 
and an update function for the same part.

The locale \<open>PartAccessBase\<close> only provides features which are not yet provided 
automatically for records by Isabelle, thus it can also be interpreted for fields
of a record type. For all other structure parts the locale \<open>PartAccess\<close> provides
the same support.
\<close>

locale PartAccessBase = PartUpdate prt_update
  for prt :: "'whol \<Rightarrow> 'part"
  and prt_update :: "('whol, 'part) PartUpdate"
+ assumes sameUpdRule[sameUpd]: "prt_update (\<lambda>_. u (prt w)) w = prt_update u w"
      and prtPrtUpdApp: "prt (prt_update u w) = u (prt w)"
begin
lemma prtPrtUpdComp[simp]: "prt \<circ> (prt_update u) = u \<circ> prt"
  by(rule ext,simp add: prtPrtUpdApp)
lemma neutrUpdRule: "prt x = v \<Longrightarrow> x = prt_update (\<lambda>_.v) x"
  by(erule subst,simp add: sameUpdRule[where u = "(\<lambda>a. a)"])
lemma idsameUpdRule[simp]: "prt_update (\<lambda>_. (prt w)) w = w"
  apply(subst id_apply[where x="(prt w)",symmetric])
  by(subst sameUpdRule,simp add: id_def)
end

locale PartAccess = PartAccessBase prt prt_update
  for prt :: "'whol \<Rightarrow> 'part"
  and prt_update :: "('whol, 'part) PartUpdate"
begin
declare prtPrtUpdApp[simp]
end

subsection \<open>Laws for Relating Two Parts\<close>

text \<open>
The locale \<open>PartComm\<close> provides the commutativity law for two modification functions
of a structure which characterizes the updates as independent. This is true for all
part update functions for different parts, since every update only depends on the
old value of its own part and not on other parts. The law is defined in a more general
way so that the locale can also be used for other independent modification functions.

When \<open>PartComm\<close> is interpreted for all pairs of parts of a structure and in all 
interpretations the part update functions are specified according to a total ordering
of all parts, the simplifier together with the lemma bucket \<open>commUpd\<close> can be used
to sort arbitrary sequences of part updates. The composition form is provided in two
variants so that the sorting also works in longer sequences of (right associative) 
update compositions.
\<close>
locale PartComm =
  fixes prt1_update :: "'whol \<Rightarrow> 'whol"
    and prt2_update :: "'whol \<Rightarrow> 'whol"
  assumes commUpdApp[commUpd]: "prt2_update (prt1_update w) = prt1_update (prt2_update w)"
begin
lemma comm2UpdComp[commUpd]: "prt2_update \<circ> prt1_update = prt1_update \<circ> prt2_update"
  by(rule ext,simp add: commUpdApp)
lemma commUpdComp[commUpd]: "f \<circ> prt2_update \<circ> prt1_update = f \<circ> prt1_update \<circ> prt2_update"
  by(rule ext,simp add: commUpdApp)
end

text \<open>
The locale \<open>PartAbsrb\<close> provides an absorption law for an observation of a part and
an update of another part or any other modification of the structure which does not 
affect the part. As for \<open>PartAccess\<close> the locale \<open>PartAbsrbBase\<close> is intended for
record fields, the locale \<open>PartAbsrb\<close> is intended for all other structure parts.

Absorption of an update by an observation is the same as preserving the observation
by the update, therefore also a preservation rule is generated.
\<close>
locale PartAbsrbBase = 
    fixes prt1 :: "'whol \<Rightarrow> 'part1"
      and prt2_update :: "'whol \<Rightarrow> 'whol"
    assumes absrbUpdApp: "prt1 (prt2_update w) = prt1 w"
begin
lemma absrbUpdComp[simp]: "prt1 \<circ> prt2_update = prt1"
  by(rule ext,simp add: absrbUpdApp)
lemma prsvPart[simp]: "prsv prt1 prt2_update"
  by(simp add: prsv_def)
end

locale PartAbsrb = PartAbsrbBase prt1 prt2_update
  for prt1 :: "'whol \<Rightarrow> 'part1"
  and prt2_update :: "'whol \<Rightarrow> 'whol"
begin
declare absrbUpdApp[simp]
end

text \<open>
The locales \<open>PartFrameBase\<close> and \<open>PartFrame\<close> combine \<open>PartComm\<close> and \<open>PartAbsrbBase\<close> or
\<open>PartAbsrb\<close>, respectively. 
\<close>
locale PartFrameBase = 
  PartComm prt1_update prt2_update
  + fst: PartAbsrbBase prt1 prt2_update
  + snd: PartAbsrbBase prt2 prt1_update
  for prt1 :: "'whol \<Rightarrow> 'part1"
  and prt1_update :: "'whol \<Rightarrow> 'whol"
  and prt2 :: "'whol \<Rightarrow> 'part2"
  and prt2_update :: "'whol \<Rightarrow> 'whol"

locale PartFrame = PartFrameBase prt1 prt1_update prt2 prt2_update
  for prt1 and prt1_update and prt2 and prt2_update
begin
declare fst.absrbUpdApp[simp] snd.absrbUpdApp[simp]
end

subsection \<open>Laws for Part Groups\<close>

text \<open>
The following locales combine all locales for single parts and part pairs for 
groups of 1-4 parts.
\<close>

locale PartGroup1Base =
    prt1: PartAccessBase prt1 prt1_update 
  for prt1 and prt1_update

locale PartGroup1 = 
    prt1: PartAccess prt1 prt1_update 
  for prt1 and prt1_update

locale PartGroup2Base = 
    PartGroup1Base prt1 prt1_update
  + prt2: PartAccessBase prt2 prt2_update
  for prt1 and prt1_update and prt2 and prt2_update
+ assumes PartFrameBaseAssmp12: "PartFrameBase prt1 (prt1_update u1) prt2 (prt2_update u2)"
begin
sublocale prt12: PartFrameBase prt1 "prt1_update u1" prt2 "prt2_update u2"
  using PartFrameBaseAssmp12 .
end

locale PartGroup2 =
    PartGroup1 prt1 prt1_update
  + prt2: PartAccess prt2 prt2_update
  for prt1 and prt1_update and prt2 and prt2_update
+ assumes PartFrameAssmp12: "PartFrame prt1 (prt1_update u1) prt2 (prt2_update u2)"
begin
sublocale prt12: PartFrame prt1 "prt1_update u1" prt2 "prt2_update u2"
  using PartFrameAssmp12 .
end

locale PartGroup3Base = 
    PartGroup2Base prt1 prt1_update prt2 prt2_update
  + prt3: PartAccessBase prt3 prt3_update
  for prt1 and prt1_update and prt2 and prt2_update and prt3 and prt3_update
+ assumes PartFrameBaseAssmp13: "PartFrameBase prt1 (prt1_update u1) prt3 (prt3_update u3)"
      and PartFrameBaseAssmp23: "PartFrameBase prt2 (prt2_update u2) prt3 (prt3_update u3)"
begin
sublocale prt13: PartFrameBase prt1 "prt1_update u1" prt3 "prt3_update u3"
  using PartFrameBaseAssmp13 .
sublocale prt23: PartFrameBase prt2 "prt2_update u2" prt3 "prt3_update u3"
  using PartFrameBaseAssmp23 .
end

locale PartGroup3 = 
    PartGroup2 prt1 prt1_update prt2 prt2_update
  + prt3: PartAccess prt3 prt3_update
  for prt1 and prt1_update and prt2 and prt2_update and prt3 and prt3_update
+ assumes PartFrameAssmp13: "PartFrame prt1 (prt1_update u1) prt3 (prt3_update u3)"
      and PartFrameAssmp23: "PartFrame prt2 (prt2_update u2) prt3 (prt3_update u3)"
begin
sublocale prt13: PartFrame prt1 "prt1_update u1" prt3 "prt3_update u3"
  using PartFrameAssmp13 .
sublocale prt23: PartFrame prt2 "prt2_update u2" prt3 "prt3_update u3"
  using PartFrameAssmp23 .
end

locale PartGroup4Base = 
    PartGroup3Base prt1 prt1_update prt2 prt2_update prt3 prt3_update
  + prt4: PartAccessBase prt4 prt4_update
  for prt1 and prt1_update and prt2 and prt2_update and prt3 and prt3_update and prt4 and prt4_update
+ assumes PartFrameBaseAssmp14: "PartFrameBase prt1 (prt1_update u1) prt4 (prt4_update u4)"
      and PartFrameBaseAssmp24: "PartFrameBase prt2 (prt2_update u2) prt4 (prt4_update u4)"
      and PartFrameBaseAssmp34: "PartFrameBase prt3 (prt3_update u3) prt4 (prt4_update u4)"
begin
sublocale prt14: PartFrameBase prt1 "prt1_update u1" prt4 "prt4_update u4"
  using PartFrameBaseAssmp14 .
sublocale prt24: PartFrameBase prt2 "prt2_update u2" prt4 "prt4_update u4"
  using PartFrameBaseAssmp24 .
sublocale prt34: PartFrameBase prt3 "prt3_update u3" prt4 "prt4_update u4"
  using PartFrameBaseAssmp34 .
end

locale PartGroup4 = 
    PartGroup3 prt1 prt1_update prt2 prt2_update prt3 prt3_update
  + prt4: PartAccess prt4 prt4_update
  for prt1 and prt1_update and prt2 and prt2_update and prt3 and prt3_update and prt4 and prt4_update
+ assumes PartFrameAssmp14: "PartFrame prt1 (prt1_update u1) prt4 (prt4_update u4)"
      and PartFrameAssmp24: "PartFrame prt2 (prt2_update u2) prt4 (prt4_update u4)"
      and PartFrameAssmp34: "PartFrame prt3 (prt3_update u3) prt4 (prt4_update u4)"
begin
sublocale prt14: PartFrame prt1 "prt1_update u1" prt4 "prt4_update u4"
  using PartFrameAssmp14 .
sublocale prt24: PartFrame prt2 "prt2_update u2" prt4 "prt4_update u4"
  using PartFrameAssmp24 .
sublocale prt34: PartFrame prt3 "prt3_update u3" prt4 "prt4_update u4"
  using PartFrameAssmp34 .
end

locale PartUnit1Cnstr = 
  fixes whol :: "'part1 \<Rightarrow> 'whol"
    and prt1 :: "'whol \<Rightarrow> 'part1"
    and prt1_update :: "('whol, 'part1) PartUpdate"
  assumes allUpdApp[allUpd]: 
    "prt1_update u1 w = whol (u1 (prt1 w))"
begin
lemma allUpdComp[allUpd]: 
  "(prt1_update u1) = (\<lambda>w . whol (u1 (prt1 w)))"
  by(rule ext,simp add: allUpdApp)
end

locale PartUnit2Cnstr = 
  fixes whol :: "'part1 \<Rightarrow> 'part2 \<Rightarrow> 'whol"
    and prt1 :: "'whol \<Rightarrow> 'part1"
    and prt1_update :: "('whol, 'part1) PartUpdate"
    and prt2 :: "'whol \<Rightarrow> 'part2"
    and prt2_update :: "('whol, 'part2) PartUpdate"
  assumes allUpdApp[allUpd]: 
    "prt1_update u1 (prt2_update u2 w) = 
     whol (u1 (prt1 w)) (u2 (prt2 w))"
begin
lemma allUpdComp[allUpd]: 
  "(prt1_update u1) \<circ> (prt2_update u2) = 
   (\<lambda>w . whol (u1 (prt1 w)) (u2 (prt2 w)))"
  by(rule ext,simp add: allUpdApp)
end

locale PartUnit3Cnstr = 
  fixes whol :: "'part1 \<Rightarrow> 'part2 \<Rightarrow> 'part3 \<Rightarrow> 'whol"
    and prt1 :: "'whol \<Rightarrow> 'part1"
    and prt1_update :: "('whol, 'part1) PartUpdate"
    and prt2 :: "'whol \<Rightarrow> 'part2"
    and prt2_update :: "('whol, 'part2) PartUpdate"
    and prt3 :: "'whol \<Rightarrow> 'part3"
    and prt3_update :: "('whol, 'part3) PartUpdate"
  assumes allUpdApp[allUpd]: 
    "prt1_update u1 (prt2_update u2 (prt3_update u3 w)) = 
     whol (u1 (prt1 w)) (u2 (prt2 w)) (u3 (prt3 w))"
begin
lemma allUpdComp[allUpd]: 
  "(prt1_update u1) \<circ> (prt2_update u2) \<circ> (prt3_update u3) = 
   (\<lambda>w . whol (u1 (prt1 w)) (u2 (prt2 w)) (u3 (prt3 w)))"
  by(rule ext,simp add: allUpdApp)
end

locale PartUnit4Cnstr = 
  fixes whol :: "'part1 \<Rightarrow> 'part2 \<Rightarrow> 'part3 \<Rightarrow> 'part4 \<Rightarrow> 'whol"
    and prt1 :: "'whol \<Rightarrow> 'part1"
    and prt1_update :: "('whol, 'part1) PartUpdate"
    and prt2 :: "'whol \<Rightarrow> 'part2"
    and prt2_update :: "('whol, 'part2) PartUpdate"
    and prt3 :: "'whol \<Rightarrow> 'part3"
    and prt3_update :: "('whol, 'part3) PartUpdate"
    and prt4 :: "'whol \<Rightarrow> 'part4"
    and prt4_update :: "('whol, 'part4) PartUpdate"
  assumes allUpdApp[allUpd]: 
    "prt1_update u1 (prt2_update u2 (prt3_update u3 (prt4_update u4 w))) = 
     whol (u1 (prt1 w)) (u2 (prt2 w)) (u3 (prt3 w)) (u4 (prt4 w))"
begin
lemma allUpdComp[allUpd]: 
  "(prt1_update u1) \<circ> (prt2_update u2) \<circ> (prt3_update u3) \<circ> (prt4_update u4) = 
   (\<lambda>w . whol (u1 (prt1 w)) (u2 (prt2 w)) (u3 (prt3 w)) (u4 (prt4 w)))"
  by(rule ext,simp add: allUpdApp)
end

locale PartUnit1Base = 
    PartUnit1Cnstr whol prt1 prt1_update
  + PartGroup1Base prt1 prt1_update
  for whol and prt1 and prt1_update

locale PartUnit2Base =
    PartUnit2Cnstr whol prt1 prt1_update prt2 prt2_update
  + PartGroup2Base prt1 prt1_update prt2 prt2_update
  for whol and prt1 and prt1_update and prt2 and prt2_update

locale PartUnit3Base = 
    PartUnit3Cnstr whol prt1 prt1_update prt2 prt2_update prt3 prt3_update
  + PartGroup3Base prt1 prt1_update prt2 prt2_update prt3 prt3_update
  for whol and prt1 and prt1_update and prt2 and prt2_update and prt3 and prt3_update

locale PartUnit4Base = 
    PartUnit4Cnstr whol prt1 prt1_update prt2 prt2_update prt3 prt3_update prt4 prt4_update
  + PartGroup4Base prt1 prt1_update prt2 prt2_update prt3 prt3_update prt4 prt4_update
  for whol and prt1 and prt1_update and prt2 and prt2_update and prt3 and prt3_update and prt4 and prt4_update

locale PartUnit1 = 
    PartUnit1Cnstr whol prt1 prt1_update
  + PartGroup1 prt1 prt1_update
  for whol and prt1 and prt1_update

locale PartUnit2 =
    PartUnit2Cnstr whol prt1 prt1_update prt2 prt2_update
  + PartGroup2 prt1 prt1_update prt2 prt2_update
  for whol and prt1 and prt1_update and prt2 and prt2_update

locale PartUnit3 = 
    PartUnit3Cnstr whol prt1 prt1_update prt2 prt2_update prt3 prt3_update
  + PartGroup3 prt1 prt1_update prt2 prt2_update prt3 prt3_update
  for whol and prt1 and prt1_update and prt2 and prt2_update and prt3 and prt3_update

locale PartUnit4 = 
    PartUnit4Cnstr whol prt1 prt1_update prt2 prt2_update prt3 prt3_update prt4 prt4_update
  + PartGroup4 prt1 prt1_update prt2 prt2_update prt3 prt3_update prt4 prt4_update
  for whol and prt1 and prt1_update and prt2 and prt2_update and prt3 and prt3_update and prt4 and prt4_update

locale ArgPartAccess =
  fixes vld :: "'whol \<Rightarrow> 'arg \<Rightarrow> bool"
    and prt :: "'arg \<Rightarrow> 'whol \<Rightarrow> 'part"
    and prt_update :: "'arg \<Rightarrow> ('whol, 'part) PartUpdate"
  assumes sameUpdRule[sameUpd]: "prt_update i (\<lambda>_. u (prt i a)) a = prt_update i u a"
      and distUpdApp[distUpd]: "prt_update i u1 (prt_update i u2 w) = prt_update i (u1 \<circ> u2) w"
      and identUpdRule[simp]: "prt_update i (\<lambda>a. a) = (\<lambda>a. a)"
      and prtPrtUpdApp[simp]: "vld a i \<Longrightarrow> prt i (prt_update i u a) = u (prt i a)"
      and frameUpdApp[simp]: "i \<noteq> j \<Longrightarrow> prt j (prt_update i u a) = prt j a"
begin
lemma distUpdComp[distUpd]: "(prt_update i u1) \<circ> (prt_update i u2) = prt_update i (u1 \<circ> u2)"
  by(rule ext,simp add: distUpdApp)
lemma frameUpdComp[simp]: "i \<noteq> j \<Longrightarrow> (prt i) \<circ> (prt_update j u) = (prt i)"
  by(rule ext,simp)
end

locale PartAbsrbArg = 
    fixes vld :: "'whol \<Rightarrow> 'arg \<Rightarrow> bool"
      and prt1 :: "'arg \<Rightarrow> 'whol \<Rightarrow> 'part1"
      and prt2_update :: "'arg \<Rightarrow> 'whol \<Rightarrow> 'whol"
    assumes absrbUpdApp[simp]: "vld w i \<Longrightarrow> prt1 i (prt2_update i w) = prt1 i w"

locale PartCommArg =
  fixes prt1_update :: "'arg \<Rightarrow> 'whol \<Rightarrow> 'whol"
    and prt2_update :: "'arg \<Rightarrow> 'whol \<Rightarrow> 'whol"
  assumes commUpdApp[commUpd]: "prt2_update i (prt1_update i w) = prt1_update i (prt2_update i w)"
begin
lemma comm2UpdComp[commUpd]: "prt2_update i \<circ> prt1_update i = prt1_update i \<circ> prt2_update i"
  by(rule ext,simp add: commUpdApp)
lemma commUpdComp[commUpd]: "f \<circ> prt2_update i \<circ> prt1_update i = f \<circ> prt1_update i \<circ> prt2_update i"
  by(rule ext,simp add: commUpdApp)
end

locale PartFrameArg =
  PartCommArg prt1_update prt2_update
  + fst: PartAbsrbArg vld prt1 prt2_update
  + snd: PartAbsrbArg vld prt2 prt1_update
  for vld :: "'whol \<Rightarrow> 'arg \<Rightarrow> bool"
  and prt1 :: "'arg \<Rightarrow> 'whol \<Rightarrow> 'part1"
  and prt1_update :: "'arg \<Rightarrow> 'whol \<Rightarrow> 'whol"
  and prt2 :: "'arg \<Rightarrow> 'whol \<Rightarrow> 'part2"
  and prt2_update :: "'arg \<Rightarrow> 'whol \<Rightarrow> 'whol"




locale Arg1PartComm = 
    fixes prt1_update :: "'arg \<Rightarrow> ('whol, 'part1) PartUpdate"
      and prt2_update :: "('whol, 'part2) PartUpdate"
    assumes commUpdApp[commUpd]: "prt2_update u2 (prt1_update i u1 w) = prt1_update i u1 (prt2_update u2 w)"
begin
lemma comm2UpdComp[commUpd]: "(prt2_update u2) \<circ> (prt1_update i u1) = (prt1_update i u1) \<circ> (prt2_update u2)"
  by(rule ext,simp add: commUpdApp)
lemma commUpdComp[commUpd]: "f \<circ> (prt2_update u2) \<circ> (prt1_update i u1) = f \<circ> (prt1_update i u1) \<circ> (prt2_update u2)"
  by(rule ext,simp add: commUpdApp)
end

locale Arg1PartFrame =
(* we cannot extend Arg1PartComm because that alters the argument order *)
    fixes prt1 :: "'arg \<Rightarrow> 'whol \<Rightarrow> 'part1"
      and prt1_update :: "'arg \<Rightarrow> ('whol, 'part1) PartUpdate"
      and prt2 :: "'whol \<Rightarrow> 'part2"
      and prt2_update :: "('whol, 'part2) PartUpdate"
    assumes frameUpdApp1: "prt1 i (prt2_update u2 w) = prt1 i w"
        and frameUpdApp2: "prt2 (prt1_update i u1 w) = prt2 w"
        and commUpdApp[commUpd]: "prt2_update u2 (prt1_update i u1 w) = prt1_update i u1 (prt2_update u2 w)"
begin
lemma frameUpdComp1[simp]: "(prt1 i) \<circ> (prt2_update u2) = prt1 i"
  by(rule ext,simp add: frameUpdApp1)
lemma frameUpdComp2[simp]: "prt2 \<circ> (prt1_update i u1) = prt2"
  by(rule ext,simp add: frameUpdApp2)
lemma comm2UpdComp[commUpd]: "(prt2_update u2) \<circ> (prt1_update i u1) = (prt1_update i u1) \<circ> (prt2_update u2)"
  by(rule ext,simp add: commUpdApp)
lemma commUpdComp[commUpd]: "f \<circ> (prt2_update u2) \<circ> (prt1_update i u1) = f \<circ> (prt1_update i u1) \<circ> (prt2_update u2)"
  by(rule ext,simp add: commUpdApp)
end

locale Arg2PartComm = 
    fixes prt1_update :: "('whol, 'part1) PartUpdate"
      and prt2_update :: "'arg \<Rightarrow> ('whol, 'part2) PartUpdate"
    assumes commUpdApp[commUpd]: "prt2_update i u2 (prt1_update u1 w) = prt1_update u1 (prt2_update i u2 w)"
begin
lemma comm2UpdComp[commUpd]: "(prt2_update i u2) \<circ> (prt1_update u1) = (prt1_update u1) \<circ> (prt2_update i u2)"
  by(rule ext,simp add: commUpdApp)
lemma commUpdComp[commUpd]: "f \<circ> (prt2_update i u2) \<circ> (prt1_update u1) = f \<circ> (prt1_update u1) \<circ> (prt2_update i u2)"
  by(rule ext,simp add: commUpdApp)
end

locale Arg2PartFrame =
(* we cannot extend Arg2PartComm because that alters the argument order *)
    fixes prt1 :: "'whol \<Rightarrow> 'part1"
      and prt1_update :: "('whol, 'part1) PartUpdate"
      and prt2 :: "'arg \<Rightarrow> 'whol \<Rightarrow> 'part2"
      and prt2_update :: "'arg \<Rightarrow> ('whol, 'part2) PartUpdate"
    assumes frameUpdApp1: "prt1 (prt2_update i u2 w) = prt1 w"
        and frameUpdApp2: "prt2 i (prt1_update u1 w) = prt2 i w"
        and commUpdApp[commUpd]: "prt2_update i u2 (prt1_update u1 w) = prt1_update u1 (prt2_update i u2 w)"
begin
lemma frameUpdComp1[simp]: "prt1 \<circ> (prt2_update i u2) = prt1"
  by(rule ext,simp add: frameUpdApp1)
lemma frameUpdComp2[simp]: "(prt2 i) \<circ> (prt1_update u1) = prt2 i"
  by(rule ext,simp add: frameUpdApp2)
lemma comm2UpdComp[commUpd]: "(prt2_update i u2) \<circ> (prt1_update u1) = (prt1_update u1) \<circ> (prt2_update i u2)"
  by(rule ext,simp add: commUpdApp)
lemma commUpdComp[commUpd]: "f \<circ> (prt2_update i u2) \<circ> (prt1_update u1) = f \<circ> (prt1_update u1) \<circ> (prt2_update i u2)"
  by(rule ext,simp add: commUpdApp)
end

lemma sameUpd_comp:
 "\<lbrakk>\<And> u a. upd1 (\<lambda>_. u (acc1 a)) a = upd1 u a;
   \<And> u a. upd2 (\<lambda>_. u (acc2 a)) a = upd2 u a\<rbrakk> \<Longrightarrow>
  (upd1 \<circ> upd2) (\<lambda>_. u ((acc2 \<circ> acc1) a)) a = (upd1 \<circ> upd2) u a"
  by (simp,metis)

end
