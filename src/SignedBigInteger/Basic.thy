theory Basic
  imports "../BigInt"
begin

text "Basic Types and definitions for signed big integers"

type_synonym signed_big_int = "big_int \<times> bool"

definition \<sigma> :: "signed_big_int \<Rightarrow> bool" where "\<sigma> \<equiv> snd"
definition limbs_of :: "signed_big_int \<Rightarrow> big_int" where "limbs_of \<equiv> fst"

definition signed_big_int_to_int :: "signed_big_int \<Rightarrow> int" where
  "signed_big_int_to_int x = (if \<not>(\<sigma> x) then int (big_int_\<alpha> $ limbs_of x) else -int (big_int_\<alpha> $ limbs_of x))"

abbreviation "signed_big_int_\<alpha> \<equiv> signed_big_int_to_int"

lemma signed_big_int_zero_\<alpha>: "signed_big_int_to_int ([], False) = 0"
  by eval

definition int_to_signed_big_int :: "int \<Rightarrow> signed_big_int" where
  "int_to_signed_big_int x = (if x < 0 then (nat_to_big_int $ nat (abs x), True) else (nat_to_big_int $ nat x, False))"

lemma signed_big_int_zero_\<gamma>: "int_to_signed_big_int 0 = ([], False)"
  by eval

text "Analogously to unsigned integers, we define a relation of signed big integers and the builtin integers.
  Also we require s = 0 for xs = [], i.e. we only allow one representation of 0."
definition "signed_big_int_invar si \<equiv> \<not>(\<sigma> si) \<and> limbs_of si = [] \<or> limbs_of si \<noteq> [] \<and> last $ limbs_of si \<noteq> 0"

lemma sigma_impl_int_sign:
  assumes "signed_big_int_invar x"
    shows "\<sigma> x \<longleftrightarrow> signed_big_int_\<alpha> x < 0"
proof
  assume "\<sigma> x"
  then have sigma_ne: "\<sigma> x"
    by simp
  with assms have ne: "limbs_of x \<noteq> []" and last_ne: "last (limbs_of x) \<noteq> 0"
    unfolding signed_big_int_invar_def by auto
  have "int (big_int_\<alpha> (limbs_of x)) > 0"
    using big_int_to_nat_not0[OF ne last_ne] by simp
  then show "signed_big_int_\<alpha> x < 0"
    using sigma_ne unfolding signed_big_int_to_int_def by simp
next
  assume "signed_big_int_\<alpha> x < 0"
  then show "\<sigma> x"
    unfolding signed_big_int_to_int_def by (auto split: if_splits)
qed

lemma signed_big_int_invar_impl_unsigned_invar:
  assumes "signed_big_int_invar x"
    shows "big_int_invar (limbs_of x)"
  using assms(1) unfolding signed_big_int_invar_def big_int_invar_def
  by auto

lemma signed_big_int_nontrivial_limbs_gt_zero:
  assumes "signed_big_int_invar x"
      and "limbs_of x \<noteq> []"
    shows "signed_big_int_\<alpha> x \<noteq> 0"
proof -
  have last_ne: "last (limbs_of x) \<noteq> 0"
    using assms unfolding signed_big_int_invar_def by auto
  have alpha_ne: "int (big_int_\<alpha> (limbs_of x)) \<noteq> 0"
    using big_int_to_nat_not0[OF assms(2) last_ne] by simp
  then show ?thesis
    unfolding signed_big_int_to_int_def by simp
qed

lemma signed_big_int_zero_unique:
  assumes "signed_big_int_invar x"
      and "signed_big_int_\<alpha> x = 0"
    shows "x = ([], False)"
proof -
  have alpha0: "big_int_\<alpha> (limbs_of x) = 0"
    using assms(2) unfolding signed_big_int_to_int_def by (simp split: if_splits)
  have empty: "limbs_of x = []"
  proof (rule ccontr)
    assume ne: "limbs_of x \<noteq> []"
    have "last (limbs_of x) \<noteq> 0"
      using assms(1) ne unfolding signed_big_int_invar_def by auto
    then have "big_int_\<alpha> (limbs_of x) \<noteq> 0"
      using big_int_to_nat_not0 ne by blast
    then show False using alpha0 by simp
  qed
  then have "\<not>(\<sigma> x)"
    using assms(1) unfolding signed_big_int_invar_def by auto
  then show ?thesis
    using \<sigma>_def empty limbs_of_def split_pairs2 by fastforce
qed

lemma signed_big_int_to_int_unique:
  assumes "signed_big_int_invar x"
      and "signed_big_int_invar x'"
      and "signed_big_int_to_int x = signed_big_int_to_int x'"
    shows "x = x'"
proof (cases "limbs_of x = [] \<and> \<not>(\<sigma> x)")
  case True
  then have x_eq: "x = ([], False)"
    by (simp add: \<sigma>_def limbs_of_def split_pairs2)
  then have "signed_big_int_to_int x = 0"
    by (metis signed_big_int_zero_\<alpha>)
  then show ?thesis
    by (metis x_eq assms(2) assms(3) signed_big_int_zero_unique)
next
  case False
  then have x_ne: "limbs_of x \<noteq> []"
    using assms(1) unfolding signed_big_int_invar_def by auto
  have last_ne: "last (limbs_of x) \<noteq> 0"
    using assms(1) x_ne unfolding signed_big_int_invar_def by auto
  have alpha_ne: "big_int_\<alpha> (limbs_of x) \<noteq> 0"
    using big_int_to_nat_not0 x_ne last_ne by blast
  have sign_eq: "\<sigma> x = \<sigma> x'"
    using assms(1,2,3) sigma_impl_int_sign by presburger
  have alpha_eq: "big_int_\<alpha> (limbs_of x) = big_int_\<alpha> (limbs_of x')"
    using assms(3) sign_eq unfolding signed_big_int_to_int_def by (auto split: if_splits)
  have uinvar_x: "big_int_invar (limbs_of x)"
    by (rule signed_big_int_invar_impl_unsigned_invar[OF assms(1)])
  have uinvar_x': "big_int_invar (limbs_of x')"
    by (rule signed_big_int_invar_impl_unsigned_invar[OF assms(2)])
  have limbs_eq: "limbs_of x = limbs_of x'"
    using big_int_to_nat_unique uinvar_x uinvar_x' alpha_eq by blast
  show ?thesis
    by (smt (verit) \<sigma>_def limbs_eq limbs_of_def sign_eq split_pairs2)
qed
  
definition "signed_big_int_rel \<equiv> br signed_big_int_to_int signed_big_int_invar"

lemma signed_big_int_rel_from_\<alpha>:
  assumes "signed_big_int_invar ai"
  shows "(ai, signed_big_int_\<alpha> ai) \<in> signed_big_int_rel"
  unfolding signed_big_int_rel_def signed_big_int_to_int_def signed_big_int_invar_def
  by (smt (verit, ccfv_threshold) assms in_br_conv signed_big_int_invar_def)

text "We can show that the signed big int relation generalizes the unsigned variant."

definition \<sigma>_int :: "signed_big_int \<Rightarrow> int" where
  "\<sigma>_int x = (if \<sigma> x then -1 else 1)"

lemma int_of_signed_big_int_alt: "signed_big_int_\<alpha> x = \<sigma>_int x * int $ big_int_\<alpha> (limbs_of x)"
  by (simp add: \<sigma>_int_def signed_big_int_to_int_def) 
  
lemma signed_big_int_rel_from_limbs:
  assumes "signed_big_int_invar ai"
      and "(limbs_of ai, a) \<in> big_int_rel"
    shows "(ai, \<sigma>_int ai * int a) \<in> signed_big_int_rel"
proof -
  have "big_int_\<alpha> (limbs_of ai) = a"
    using assms(2) unfolding big_int_rel_def in_br_conv by simp
  then have "signed_big_int_to_int ai = \<sigma>_int ai * int a"
    using int_of_signed_big_int_alt by simp
  then show ?thesis
    unfolding signed_big_int_rel_def in_br_conv using assms(1) by simp
qed

lemma signed_big_int_eq_from_big_int_and_sign:
  assumes "signed_big_int_invar ai"
      and "signed_big_int_invar bi"
      and "(limbs_of ai, n) \<in> big_int_rel"
      and "(limbs_of bi, n) \<in> big_int_rel"
      and "\<sigma> ai = \<sigma> bi"
    shows "ai = bi"
proof -
  have na: "big_int_\<alpha> (limbs_of ai) = n"
    using assms(3) unfolding big_int_rel_def in_br_conv by simp
  have nb: "big_int_\<alpha> (limbs_of bi) = n"
    using assms(4) unfolding big_int_rel_def in_br_conv by simp
  have limbs_eq: "limbs_of ai = limbs_of bi"
    using big_int_to_nat_unique
          signed_big_int_invar_impl_unsigned_invar[OF assms(1)]
          signed_big_int_invar_impl_unsigned_invar[OF assms(2)]
          na nb by simp
  show ?thesis
    using assms(1,2,5) limbs_eq signed_big_int_to_int_def signed_big_int_to_int_unique by presburger
qed

lemma signs_rel:
  assumes "(ai, a) \<in> signed_big_int_rel"
    shows "\<not>(\<sigma> ai) \<longleftrightarrow> a \<ge> 0"
      and "\<sigma> ai \<longleftrightarrow> a < 0"
  apply (smt (verit, del_insts) assms in_br_conv sigma_impl_int_sign signed_big_int_rel_def)
  apply (metis assms in_br_conv sigma_impl_int_sign signed_big_int_rel_def)
  done

lemma abs_from_limbs:
  assumes "(ai, a) \<in> signed_big_int_rel"
    shows "big_int_\<alpha> $ limbs_of ai = nat $ abs a"
  by (smt (verit, ccfv_threshold) APP_def assms in_br_conv int_eq_iff signed_big_int_rel_def signed_big_int_to_int_def)

lemma abs_rel:
  assumes "(ai, a) \<in> signed_big_int_rel"
    shows "(limbs_of ai, nat $ abs a) \<in> big_int_rel"
  by (metis APP_def abs_from_limbs assms big_int_rel_def in_br_conv signed_big_int_invar_impl_unsigned_invar signed_big_int_rel_def)

lemma signed_rel_from_int_pos:
  assumes "int $ big_int_\<alpha> ai = a"
      and "big_int_invar ai"
    shows "((ai,False),a) \<in> signed_big_int_rel"
proof -
  have "signed_big_int_\<alpha> (ai,False) = int $ big_int_\<alpha> ai"
    unfolding signed_big_int_to_int_def \<sigma>_def limbs_of_def by simp
  then have val: "signed_big_int_\<alpha> (ai,False) = a"
    using assms by simp
  have "last ai \<noteq> 0 \<or> ai = []"
    using assms(2) big_int_invar_def by auto
  then have "signed_big_int_invar (ai,False)"
    unfolding signed_big_int_invar_def \<sigma>_def limbs_of_def by auto
  then show ?thesis
    by (simp add: brI signed_big_int_rel_def val)
qed

lemma signed_rel_from_int_neg:
  assumes "int $ big_int_\<alpha> ai = a"
      and "big_int_invar ai"
      and "ai \<noteq> []"
    shows "((ai,True),-a) \<in> signed_big_int_rel"
proof -
  have "signed_big_int_\<alpha> (ai,True) = -int $ big_int_\<alpha> ai"
    unfolding signed_big_int_to_int_def \<sigma>_def limbs_of_def by simp
  then have val: "signed_big_int_\<alpha> (ai,True) = -a"
    using assms by simp
  have "signed_big_int_invar (ai,False)"
    unfolding signed_big_int_invar_def \<sigma>_def limbs_of_def
    using assms(2) assms(3)
    unfolding big_int_invar_def
    by auto
  then show ?thesis
    by (simp add: assms(3) brI limbs_of_def signed_big_int_invar_def signed_big_int_rel_def val)
qed    

end
