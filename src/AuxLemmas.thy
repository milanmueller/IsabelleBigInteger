theory AuxLemmas
  imports Main
begin 

lemma mod_div_less:
  fixes a b :: nat
  shows "a mod b + a div b \<le> a"
  by (metis add.commute add_le_imp_le_left div_by_0 div_le_dividend mod_by_0 mod_div_decomp mult.commute nat_le_linear nonzero_mult_div_cancel_left
      verit_la_disequality)

lemma mod_div_less_strict:
  fixes a b :: nat 
  assumes "2 < b" "b \<le> a"
  shows "a mod b + a div b < a"
  by (metis Suc_1 Suc_lessD add.commute add_0 add_diff_cancel_right' add_lessD1 assms(1,2) div_greater_zero_iff minus_mod_eq_mult_div mod_div_less mult.commute mult_eq_self_implies_10
      nat_less_le)

find_unused_assms
unused_thms

end