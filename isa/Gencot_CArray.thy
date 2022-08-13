theory Gencot_CArray
  imports ShallowShared
    Gencot_Default
begin

section \<open>Gencot Array Operations\<close>

text \<open>
Non-tuples form. For detailed description see theory \<open>Gencot_CArray_Tuples\<close>.
\<close>

subsection \<open>Definitions for the Gencot Array Operations\<close>

consts
  toPtr :: "'el \<Rightarrow> 'pel"
  frPtr :: "'pel \<Rightarrow> 'el"

locale CArrayDefs = 
  fixes arr :: "'carr \<Rightarrow> 'el list"
    and arr_update :: "('el list \<Rightarrow> 'el list) \<Rightarrow> 'carr \<Rightarrow> 'carr"
    and siz :: "'carr \<Rightarrow> nat"
    and idxtypespec :: "('m::len) word"
begin
definition getArr :: "('carr, 'm word) Tup2 \<Rightarrow> 'el"
  where "getArr arg \<equiv> let c = p1Tup2 arg; i = p2Tup2 arg in 
            if unat i \<ge> siz c then hd (arr c) else (nth (arr c) (unat i))"
definition setArr :: "('carr, 'm word, 'el) Tup3 \<Rightarrow> ('carr, unit) Tup2"
  where "setArr arg \<equiv> let c = p1Tup3 arg; i = p2Tup3 arg; e = p3Tup3 arg in 
            makeTup2 (if unat i \<ge> siz c then c else arr_update (\<lambda>a. (list_update a (unat i) e)) c) ()"
definition modifyArr :: "('carr, 'm word, (('el, 'arg) Tup2 \<Rightarrow> ('el, 'out) Tup2), 'arg) Tup4 \<Rightarrow> ('carr, 'out) Tup2"
  where "modifyArr arg \<equiv> 
    let c = p1Tup4 arg; idx = p2Tup4 arg; u = p3Tup4 arg; inp = p4Tup4 arg;
        i = (if unat idx \<ge> siz c then 0 else unat idx);
        ures = u (makeTup2 (nth (arr c) i) inp) 
    in makeTup2 (arr_update (\<lambda>a. (list_update a i (p1Tup2 ures))) c) (p2Tup2 ures)"
definition modrefArr :: "('carr, 'm word, (('pel, 'arg) Tup2 \<Rightarrow> ('pel, 'out) Tup2 ), 'arg) Tup4 \<Rightarrow> ('carr, 'out) Tup2"
  where "modrefArr arg \<equiv> 
    let c = p1Tup4 arg; idx = p2Tup4 arg; u = p3Tup4 arg; inp = p4Tup4 arg; 
        i = (if unat idx \<ge> siz c then 0 else unat idx); 
        ures = u(makeTup2 (toPtr (nth (arr c) i)) inp)
    in makeTup2 (arr_update (\<lambda>a. (list_update a i (frPtr (p1Tup2 ures)))) c) (p2Tup2 ures)"
end

subsubsection \<open>Explicitly sized arrays\<close>

locale ESArrBase
begin
definition arr :: "'el CArrES\<^sub>T \<Rightarrow> 'el list" 
  where "arr \<equiv> p1Tup2"
definition arr_update :: "('el list \<Rightarrow> 'el list) \<Rightarrow> 'el CArrES\<^sub>T \<Rightarrow> 'el CArrES\<^sub>T"
  where "arr_update \<equiv> p1Tup2_update"
definition siz :: "'el CArrES\<^sub>T \<Rightarrow> nat" 
  where "siz \<equiv> (unat \<circ> p2Tup2)"
definition carr :: "'el list \<Rightarrow> 'el CArrES\<^sub>T" 
  where "carr \<equiv> \<lambda>a. makeTup2 a (of_nat (length a))"
end

locale ESArrDefs = ESArrBase
begin
sublocale CArrayDefs arr arr_update siz "0::64 word" .
end

subsubsection \<open>Fixed sized arrays\<close>

locale FxdArrBase = 
  fixes arr :: "'carr \<Rightarrow> 'el list"
    and carr :: "'el list \<Rightarrow> 'carr"
    and fxdsiz :: "nat"
begin

definition siz :: "'carr \<Rightarrow> nat"
  where fxdsiz_def: "siz c \<equiv> fxdsiz"
definition arr_update :: "('el list \<Rightarrow> 'el list) \<Rightarrow> 'carr \<Rightarrow> 'carr"
  where "arr_update u \<equiv> carr \<circ> u \<circ> arr"

definition toCAES :: "'carr \<Rightarrow> 'el CArrES\<^sub>T"
  where "toCAES a \<equiv> makeTup2 (arr a) (of_nat (fxdsiz))"
definition fromCAES :: "'el CArrES\<^sub>T \<Rightarrow> 'carr"
  where "fromCAES aes \<equiv> carr (p1Tup2 aes)"
definition rotoCAES :: "'carr \<Rightarrow> 'el CArrES\<^sub>T"
  where [simp]: "rotoCAES a \<equiv> toCAES a"
definition rofromCAES :: "'el CArrES\<^sub>T \<Rightarrow> 'carr"
  where [simp]: "rofromCAES aes \<equiv> fromCAES aes"

end

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
