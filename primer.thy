theory AbstractGeometry
imports Main
begin


definition moduo :: "nat \<Rightarrow> nat \<Rightarrow> bool" (infix "\<approx>" 50) where
 "a \<approx> b \<longleftrightarrow> (\<exists> m. m \<noteq> (0::nat) \<and> a mod m = b mod m)"

lemma moduo_eq_refl:
  "a \<approx> a"
by (simp add: moduo_def, rule_tac x = 1 in exI, auto) 

lemma moduo_eq_sym:
  assumes "a \<approx> b"
  shows "b \<approx> a"
using assms
by (simp add: moduo_def, auto)

lemma moduo_eq_trans:
  assumes "a \<approx> b"  "b \<approx> c"
  shows "a \<approx> c"
using assms 
by (simp add: moduo_def, auto)

thm "equivpI"

text {* Quotient of moduo*}
quotient_type 
  moduo_qt = nat / "moduo"
apply (rule equivpI, rule reflpI, simp add: moduo_eq_refl)
apply (rule sympI, simp add: moduo_eq_sym)
apply (rule transpI, blast intro: moduo_eq_trans)
done

definition add_moduo :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
  "add_moduo a b c = (a + b) * c"

lift_definition add :: "moduo_qt \<Rightarrow> moduo_qt \<Rightarrow> moduo_qt \<Rightarrow> moduo_qt" is add_moduo
apply (simp add: add_moduo_def moduo_def)
by auto

lemma add_homo_commute: "add a b c = add b a c"
apply transfer
apply (simp add: add_moduo_def moduo_def)
by auto


lemma "((A \<longrightarrow> B) \<longrightarrow> A) \<longrightarrow> A"
proof
  assume "(A \<longrightarrow> B) \<longrightarrow> A"
  show A
  proof(rule classical)
    assume "\<not> A"
    have "(A \<longrightarrow> B)"
    proof
      assume "A"
      with `\<not> A` show "B" by contradiction
    qed
    with `(A \<longrightarrow> B) \<longrightarrow> A` show A ..
  qed
qed


lemma "((A \<longrightarrow> B) \<longrightarrow> A) \<longrightarrow> A"
apply (rule impI)+
apply (rule classical)
apply (erule impE)
apply (rule impI)
apply (erule notE, assumption)+
done


end