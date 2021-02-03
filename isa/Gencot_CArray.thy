theory Gencot_CArray
  imports ShallowShared
    Gencot_Default
begin

text \<open>First we define the array functions for fixed lists\<close>

definition getArr' :: "('n::finite, 'el) FixedList \<Rightarrow> 32 word \<Rightarrow> 'el"
  where 
    "getArr' lst idx \<equiv>
      if unat idx >= CARD('n) then hd (Rep_FixedList lst)
      else (nth (Rep_FixedList lst) (unat idx))"

definition setArr' :: "('n::finite, 'el) FixedList \<Rightarrow> (32 word, 'el) RR \<Rightarrow> ('n, 'el) FixedList"
  where
    "setArr' lst arg2 \<equiv> 
      let idx =  RR.p1\<^sub>f arg2; elm =  RR.p2\<^sub>f arg2 in
        if unat idx >= CARD('n) then lst
        else (Abs_FixedList (list_update (Rep_FixedList lst) (unat idx) elm))"

definition modifyArrDflt' :: "('n::finite, 'el) FixedList \<Rightarrow> (32 word, ('el, 'arg) RR \<Rightarrow> ('el, 'out) RR, 'arg) Tup3 \<Rightarrow> ('n, 'el) FixedList \<times> 'out"
  where
    "modifyArrDflt' lst arg2 \<equiv> 
        let idx = Tup3.p1\<^sub>f arg2; chf = Tup3.p2\<^sub>f arg2; inp = Tup3.p3\<^sub>f arg2 in
          if unat idx >= CARD('n) then (lst, defaultVal ())
          else let l = Rep_FixedList lst; elm = nth l (unat idx)
               in (Abs_FixedList (list_update l (unat idx) (RR.p1\<^sub>f (chf (RR.make elm inp )))), defaultVal ())"

text \<open>
  This locale has the wrapper record access and constructor as parameters.
  It defines the array functions for the wrapper record and proves some useful lemmas.\<close>

locale CArrFuns = fixes fld :: "'arr \<Rightarrow> ('n::finite, 'el) FixedList" and wrp :: "('n, 'el) FixedList \<Rightarrow> 'arr"
begin
definition getArrFxd :: "('arr, 32 word) RR \<Rightarrow> 'el"
  where "getArrFxd arg \<equiv>
  let arrlst = fld (RR.p1\<^sub>f arg); idx = RR.p2\<^sub>f arg in getArr' arrlst idx"
definition setArrFxd :: "('arr, (32 word, 'el) RR) RR \<Rightarrow> ('arr, unit) RR"
  where "setArrFxd arg \<equiv>
  let arrlst = fld (RR.p1\<^sub>f arg); arg2 = RR.p2\<^sub>f arg in RR.make (wrp(setArr' arrlst arg2)) ()"
definition modifyArrDfltFxd :: "('arr, (32 word, ('el, 'arg) RR \<Rightarrow> ('el, 'out) RR, 'arg) Tup3) RR \<Rightarrow> ('arr, 'out) RR"
  where "modifyArrDfltFxd arg \<equiv>
  let arrlst = fld (RR.p1\<^sub>f arg); arg2 = RR.p2\<^sub>f arg; (reslst,res) = modifyArrDflt' arrlst arg2 in RR.make (wrp reslst) res"

text \<open>Arrays are never empty.\<close>
lemma arrNotNil: "\<forall>x::'arr .  (Rep_FixedList (fld  x)) \<noteq> []"
  apply(rule allI)
  apply(cut_tac x = "(fld (x::'arr))" for el in Rep_FixedList )
  apply(auto)
  done
end

end
