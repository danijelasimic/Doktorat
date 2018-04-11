theory bla
imports Main
begin

fun ins :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "ins a (x#y#xs) = x # a # (ins a (y#xs))"
| "ins a [] = []"
| "ins a [v] = [v, a]"

lemma "ins a x @ ins a y = ins a (x @ y)"
proof(induct x rule:ins.induct)
(*
apply (induct x rule:ins.induct)
apply (simp add:ins.simps)+
apply (induct y rule:ins.induct)
by (simp add:ins.simps)+
*)
  case (1 a x p q)
  assume "ins a (p # q) @ ins a y = ins a ((p # q) @ y)"
  thus ?case
    by simp
next
  case (2 a)
  show ?case
    by simp
next
  case (3 a v)
  show ?case
    (* I nacin: by (metis append_Cons append_Nil ins.simps(1) ins.simps(2) ins.simps(3) list.exhaust)*)
    (* II nacin: apply (induct y rule:ins.induct)
                 apply simp+
    *)
    proof(induct y rule:ins.induct)
      case (1 m x y t)
      show ?case
        by simp
    next
      case (2 m) 
      show ?case
        by simp
    next
      case (3 m v)
      show ?case
        by simp
    qed
qed

end