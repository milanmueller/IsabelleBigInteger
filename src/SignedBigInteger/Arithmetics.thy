theory Arithmetics 
  imports Basic UnsignedArithmetics
begin

section \<open>Inversion\<close>

definition \<open>sbi_inv \<equiv> \<lambda>(l,\<sigma>). if l = [] then (l,\<sigma>) else (l,\<not>\<sigma>)\<close>

lemma sbi_inv_correct: \<open>signed_big_int_\<alpha> $ sbi_inv x = - signed_big_int_\<alpha> x\<close>
  by (smt (verit, ccfv_threshold) APP_def \<sigma>_def limbs_of_def prod.simps(2)
    sbi_inv_def signed_big_int_to_int_def signed_big_int_zero_\<alpha>
    split_pairs2)

lemma sbi_inv_ref:
  \<open>(RETURN o sbi_inv, RETURN o uminus) \<in> signed_big_int_rel \<rightarrow>\<^sub>f \<langle>signed_big_int_rel\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (auto simp: signed_big_int_rel_def in_br_conv)
  using sbi_inv_correct apply auto[1]
  by (smt (verit, ccfv_SIG) fst_conv limbs_of_def old.prod.case sbi_inv_def
      signed_big_int_invar_def)

section "Comparisons"

definition \<open>signed_big_int_eq a b \<equiv> doN{
    if \<sigma> a \<noteq> \<sigma> b \<or> length_fst a \<noteq> length_fst b then RETURN False
    else doN {
      ASSERT(length_fst a = length_fst b);
      (_, eq) \<leftarrow> WHILEIT 
        (\<lambda>(i, eq). i \<le> length_fst a \<and> (eq \<longleftrightarrow> take i (fst a) = take i (fst b)))
        (\<lambda>(i, eq). i < length_fst a \<and> eq)
        (\<lambda>(i, eq). doN {
            ASSERT(i < length_fst a);
            if get_or_zero_fst a i \<noteq> get_or_zero_fst b i then RETURN (i+1, False)
            else RETURN (i+1, True) 
        }) (0, True);
      RETURN eq
    } 
}\<close>

lemma signed_big_int_eq_correct:
  \<open>signed_big_int_eq a b \<le> SPEC (\<lambda>r. r \<longleftrightarrow> a = b)\<close>
  unfolding signed_big_int_eq_def
  apply (refine_vcg WHILEIT_rule[where R = \<open>measure (\<lambda>(i,_). length_fst a - i)\<close>])
  apply (clarsimp_all simp: take_Suc_conv_app_nth)
  subgoal by (auto simp: take_Suc_conv_app_nth get_or_zero_fst_def get_or_zero_def length_fst_def)
  subgoal by linarith
  subgoal by (metis get_or_zero_fst_alt_def length_fst_def take_Suc_conv_app_nth)
  subgoal by linarith
  subgoal 
    apply auto
    apply (simp add: \<sigma>_def length_fst_def prod_eqI)
    by (simp add: \<sigma>_def length_fst_def prod_eq_iff)
  done

lemma signed_big_int_eq_refine:
  \<open>(uncurry signed_big_int_eq, uncurry (RETURN oo (=)))
     \<in> signed_big_int_rel \<times>\<^sub>r signed_big_int_rel \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply clarsimp
  apply (rule order_trans[OF signed_big_int_eq_correct])
  apply refine_vcg
  by (metis in_br_conv signed_big_int_rel_def signed_big_int_to_int_unique)

text \<open>Sepref's id-phase pattern rule @{thm op_neq_pat} rewrites \<open>a \<noteq> b\<close> into \<open>op_neq a b\<close>,
  so every type with a custom eq-operator also needs an @{const op_neq} implementation.\<close>

definition signed_big_int_neq :: "signed_big_int \<Rightarrow> signed_big_int \<Rightarrow> bool nres" where
  "signed_big_int_neq a b = doN { eq \<leftarrow> signed_big_int_eq a b; RETURN (\<not>eq) }"

lemma signed_big_int_neq_correct:
  \<open>signed_big_int_neq a b \<le> SPEC (\<lambda>r. r \<longleftrightarrow> a \<noteq> b)\<close>
  using signed_big_int_eq_correct[of a b]
  unfolding signed_big_int_neq_def
  by (auto simp: pw_le_iff refine_pw_simps)

lemma signed_big_int_neq_refine:
  \<open>(uncurry signed_big_int_neq, uncurry (RETURN oo op_neq))
     \<in> signed_big_int_rel \<times>\<^sub>r signed_big_int_rel \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply clarsimp
  apply (rule order_trans[OF signed_big_int_neq_correct])
  apply refine_vcg
  by (metis in_br_conv signed_big_int_rel_def signed_big_int_to_int_unique)

section "Constants"

definition signed_big_int0 :: signed_big_int where
  "signed_big_int0 \<equiv> ([], False)"

lemma signed_big_int0_refine: "(signed_big_int0, 0) \<in> signed_big_int_rel"
  by (auto simp: signed_big_int0_def signed_big_int_rel_def in_br_conv
      signed_big_int_zero_\<alpha> signed_big_int_invar_def \<sigma>_def limbs_of_def)

definition signed_big_int1 :: signed_big_int where
  "signed_big_int1 \<equiv> ([1], False)"

lemma signed_big_int1_refine: "(signed_big_int1, 1) \<in> signed_big_int_rel"
  by (auto simp: signed_big_int1_def signed_big_int_rel_def in_br_conv
      signed_big_int_one_\<alpha> signed_big_int_invar_def \<sigma>_def limbs_of_def)

section "Arithmetic Operations"

subsection "Addition"
text "We can consider two cases: The signs of the inputs are equal, or they are not."

definition signed_big_int_add_\<sigma>_eq :: "signed_big_int \<Rightarrow> signed_big_int \<Rightarrow> signed_big_int nres" where
  "signed_big_int_add_\<sigma>_eq ai bi = doN {
    let (\<sigma>\<^sub>a, \<sigma>\<^sub>b) = (\<sigma> ai, \<sigma> bi);
    ASSERT(\<sigma>\<^sub>a = \<sigma>\<^sub>b);
    ri \<leftarrow> signed_big_int_abs_add ai bi;
    RETURN(ri, \<sigma>\<^sub>a)
  }"

lemma signed_big_int_add_\<sigma>_eq_correct:
  assumes "(ai, a) \<in> signed_big_int_rel"
      and "(bi, b) \<in> signed_big_int_rel"
      and "\<sigma> ai = \<sigma> bi"
    shows "signed_big_int_add_\<sigma>_eq ai bi \<le> \<Down>signed_big_int_rel (RETURN (a + b))"
  unfolding signed_big_int_add_\<sigma>_eq_def \<sigma>_def
  apply (refine_vcg assms signed_big_int_abs_add_correct[OF assms(1) assms(2)])
  using \<sigma>_def assms(3) apply force
  subgoal premises prems for \<sigma>\<^sub>a \<sigma>\<^sub>b r
  proof (cases \<sigma>\<^sub>a)
    case True
    have sign_a: "a < 0"
      using True \<sigma>_def assms(1) prems(1) signs_rel(2) by auto
    have sign_b: "b < 0"
      using assms(1,2,3) sign_a signs_rel(2) by blast
    have r_val: "int $ big_int_\<alpha> r = -(a + b)"
      using prems sign_a sign_b by (simp add: int_ops)
    have r_ne: "r \<noteq> []"
      using prems sign_a sign_b by fastforce
    show ?thesis
      by (smt (verit, best) True prems(3) r_ne r_val signed_rel_from_int_neg)
  next
    case False
    have sign_a: "a \<ge> 0"
      using False \<sigma>_def assms(1) prems(1) signs_rel(2) by auto
    have sign_b: "b \<ge> 0"
      using assms(1,2,3) sign_a signs_rel(2) by auto
    have r_val: "int $ big_int_\<alpha> r = a + b"
      using prems sign_a sign_b by (simp add: int_ops)
    show ?thesis using prems False r_val signed_rel_from_int_pos by fastforce
  qed
  done

definition signed_big_int_add_\<sigma>_neq :: "signed_big_int \<Rightarrow> signed_big_int \<Rightarrow> signed_big_int nres" where
  "signed_big_int_add_\<sigma>_neq ai bi = doN {
    let (\<sigma>\<^sub>a, \<sigma>\<^sub>b) = (\<sigma> ai, \<sigma> bi);
    ASSERT(\<sigma>\<^sub>a \<noteq> \<sigma>\<^sub>b);
    if \<sigma>\<^sub>a then do {
      neg_le \<leftarrow> signed_big_int_abs_leq ai bi;
      if neg_le then do {
        ci \<leftarrow> signed_big_int_sub_abs_compl bi ai;
        RETURN (ci, False)
      } else do {
        ci \<leftarrow> signed_big_int_sub_abs_compl ai bi;
        RETURN (ci, True)
      }
    }
    else do {
      neg_le \<leftarrow> signed_big_int_abs_leq bi ai;
      if neg_le then do {
        ci \<leftarrow> signed_big_int_sub_abs_compl ai bi;
        RETURN (ci, False)
      } else do {
        ci \<leftarrow> signed_big_int_sub_abs_compl bi ai;
        RETURN (ci, True)
      }
    }
  }"

lemma signed_big_int_add_\<sigma>_neq_correct:
  assumes "(ai, a) \<in> signed_big_int_rel"
      and "(bi, b) \<in> signed_big_int_rel"
      and "\<sigma> ai \<noteq> \<sigma> bi"
  shows "signed_big_int_add_\<sigma>_neq ai bi \<le> \<Down>signed_big_int_rel (RETURN (a + b))"
  unfolding signed_big_int_add_\<sigma>_neq_def 
  apply (cases "\<sigma> ai") 
  using assms apply auto
  subgoal premises prems
    apply (cases "nat $ abs a \<le> nat $ abs b")
      subgoal premises prems_inner
        apply (refine_vcg
          signed_big_int_abs_leq_correct'[OF prems(2) prems(3)]
          signed_big_int_sub_abs_compl_correct'[OF prems_inner(1) prems(3) prems(2)]
          signed_big_int_sub_abs_compl_correct'[OF _ prems(2) prems(3)]
        )
        subgoal premises prems_isar for cmp r proof -
          have "nat $ abs a \<le> nat $ abs b" using prems_isar by auto
          have "big_int_\<alpha> r = nat $ abs b - nat $ abs a" using prems_isar by auto
          have r_invar: "big_int_invar r"
            by (metis prems_isar(3))
          have "\<sigma> ai" using prems by auto
          then have "a < 0" by (metis prems(2) signs_rel(2))
          have "\<not>\<sigma> bi" using prems by auto
          then have "0 \<le> b" by (metis prems(3) signs_rel(1))
          then have sum_alt: "a + b = int (nat $ abs b - nat $ abs a)"
            using \<open>a < 0\<close> prems_inner by auto
          then have r_false_eval: "signed_big_int_\<alpha> (r,False) = a + b"
            by (metis APP_def \<sigma>_def limbs_of_def prems_isar(3) prod.sel(1,2) signed_big_int_to_int_def)
          then show ?thesis
            by (metis in_br_conv r_invar signed_big_int_rel_def signed_rel_from_int_pos)
        qed
        subgoal
          by linarith
        subgoal
          using prems_inner by blast
        done
      subgoal premises prems_inner proof -
        thm prems_inner
        have ord: "nat $ abs b \<le> nat $ abs a"
          using nat_le_linear prems_inner by blast
        show ?thesis
        apply (refine_vcg
          signed_big_int_abs_leq_correct'[OF prems(2) prems(3)]
          signed_big_int_sub_abs_compl_correct'[OF ord prems(2) prems(3)]
          signed_big_int_sub_abs_compl_correct'[OF _ prems(3) prems(2)]
        )
        apply simp
        subgoal using prems_inner by auto
        subgoal
          by (smt (verit, ccfv_threshold) APP_def big_int_to_nat.simps(1)
                cancel_comm_monoid_add_class.diff_cancel int_nat_eq int_ops(6) nat_le_iff
                prems(1,2,3,4) signed_rel_from_int_neg signs_rel(1))
        done
      qed
      done
  subgoal premises prems
    apply (cases "nat $ abs a \<le> nat $ abs b")
    subgoal premises prems_inner
      apply (refine_vcg
        signed_big_int_abs_leq_correct'[OF prems(3) prems(2)]
        signed_big_int_sub_abs_compl_correct'[OF prems_inner(1) prems(3) prems(2)]
        signed_big_int_sub_abs_compl_correct'[OF _ prems(2) prems(3)]
      )
      subgoal by auto
      subgoal premises prems_isar for cmp r proof -
        have "nat $ abs b \<le> nat $ abs a" using prems_isar by auto
        have "big_int_\<alpha> r = nat $ abs a - nat $ abs b" using prems_isar by auto
        have r_invar: "big_int_invar r" by (metis prems_isar(3))
        have "\<not>\<sigma> ai" using prems by auto
        then have "a \<ge> 0" by (metis signs_rel(1) prems(2))
        have "\<sigma> bi" using prems by auto
        then have "b < 0" by (metis prems(4) signs_rel(2) prems(3))
        then have sum_alt: "a + b = int (nat $ abs a - nat $ abs b)"
          using \<open>0 \<le> a\<close> \<open>nat $ \<bar>b\<bar> \<le> nat $ \<bar>a\<bar>\<close> by force
        then have r_false_eval: "signed_big_int_\<alpha> (r,False) = a + b"
          by (metis APP_def \<sigma>_def limbs_of_def prems_isar(3) prod.sel(1,2) signed_big_int_to_int_def)
        then show ?thesis
          by (metis in_br_conv r_invar signed_big_int_rel_def signed_rel_from_int_pos)
      qed
      subgoal
        by (smt (verit, del_insts) APP_def abs_from_limbs big_int_to_nat.simps(1)
              cancel_comm_monoid_add_class.diff_cancel in_br_conv int_ops(6) nat_le_iff
              prems(1,2,3,4) signed_big_int_rel_def signed_big_int_to_int_def
              signed_rel_from_int_neg signs_rel(1))
      done
    subgoal premises prems_inner proof -
      thm prems_inner
      have ord: "nat $ abs b \<le> nat $ abs a"
        using nat_le_linear prems_inner by blast
      show ?thesis
      thm signed_big_int_abs_leq_correct'[OF prems(3) prems(2)]
      thm prems
      thm signed_big_int_sub_abs_compl_correct'[OF ord prems(2) prems(3)]
      thm signed_big_int_sub_abs_compl_correct'[OF _ prems(3) prems(2)]
      apply (refine_vcg
        signed_big_int_abs_leq_correct'[OF prems(3) prems(2)]
        signed_big_int_sub_abs_compl_correct'[OF ord prems(2) prems(3)]
        signed_big_int_sub_abs_compl_correct'[OF _ prems(3) prems(2)]
      )
      subgoal 
        by (metis APP_def abs_ge_zero diff_minus_eq_add int_nat_eq linorder_not_le
              of_nat_diff prems(1,2,3,4) signed_rel_from_int_pos signs_rel(1)
              zabs_def)
      subgoal using prems_inner by auto
      subgoal
        by (smt (verit, ccfv_threshold) APP_def big_int_to_nat.simps(1)
              cancel_comm_monoid_add_class.diff_cancel int_nat_eq int_ops(6) nat_le_iff
              prems(1,2,3,4) signed_rel_from_int_neg signs_rel(1))
      done
    qed
    done
  done

definition signed_big_int_add :: "signed_big_int \<Rightarrow> signed_big_int \<Rightarrow> signed_big_int nres" where
  "signed_big_int_add ai bi = do {
    let \<sigma>\<^sub>a = \<sigma> ai;
    let \<sigma>\<^sub>b = \<sigma> bi;
    if \<sigma>\<^sub>a \<noteq> \<sigma>\<^sub>b then do {
      if \<sigma>\<^sub>a then do {
        neg_le \<leftarrow> signed_big_int_abs_leq ai bi;
        if neg_le then do {
          ci \<leftarrow> signed_big_int_sub_abs_compl bi ai;
          RETURN (ci, False)
        } else do {
          ci \<leftarrow> signed_big_int_sub_abs_compl ai bi;
          RETURN (ci, True)
        }
      }
      else do {
        neg_le \<leftarrow> signed_big_int_abs_leq bi ai;
        if neg_le then do {
          ci \<leftarrow> signed_big_int_sub_abs_compl ai bi;
          RETURN (ci, False)
        } else do {
          ci \<leftarrow> signed_big_int_sub_abs_compl bi ai;
          RETURN (ci, True)
        }
      }
    } else do {
      ci \<leftarrow> signed_big_int_abs_add ai bi;
      RETURN (ci, \<sigma>\<^sub>a)
    }
  }"

lemma signed_big_int_add_correct:
  assumes "(ai, a) \<in> signed_big_int_rel"
      and "(bi, b) \<in> signed_big_int_rel"
    shows "signed_big_int_add ai bi \<le> \<Down>signed_big_int_rel (RETURN (a + b))"
proof (cases "\<sigma> ai = \<sigma> bi")
  case True
  have "signed_big_int_add ai bi = signed_big_int_add_\<sigma>_eq ai bi"
    unfolding signed_big_int_add_def signed_big_int_add_\<sigma>_eq_def
    using True by simp
  with signed_big_int_add_\<sigma>_eq_correct[OF assms True] show ?thesis by simp
next
  case False
  have "signed_big_int_add ai bi = signed_big_int_add_\<sigma>_neq ai bi"
    unfolding signed_big_int_add_def signed_big_int_add_\<sigma>_neq_def big_int_lt_def
    using False by simp
  with signed_big_int_add_\<sigma>_neq_correct[OF assms False] show ?thesis by simp
qed

lemma signed_big_int_add_refine:
  \<open>(uncurry signed_big_int_add, uncurry (RETURN oo (+)))
  \<in> signed_big_int_rel \<times>\<^sub>r signed_big_int_rel \<rightarrow>\<^sub>f \<langle>signed_big_int_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
     (auto simp: uncurry_def intro!: signed_big_int_add_correct)

section "Subtraction"
text "With signed addition, subtraction can easily be expressed"

definition signed_big_int_sub :: "signed_big_int \<Rightarrow> signed_big_int \<Rightarrow> signed_big_int nres" where
  "signed_big_int_sub ai bi \<equiv> signed_big_int_add ai (signed_big_int_inv bi)"

section "Multiplication"

definition signed_big_int_mult_school :: "signed_big_int \<Rightarrow> signed_big_int \<Rightarrow> signed_big_int nres"
  where "signed_big_int_mult_school ai bi \<equiv> doN {
    let (\<sigma>\<^sub>a, \<sigma>\<^sub>b) = (\<sigma> ai, \<sigma> bi);
    let \<sigma>\<^sub>r = \<sigma>\<^sub>a \<noteq> \<sigma>\<^sub>b;
    ci \<leftarrow> signed_big_int_mult_school_aux ai bi;
    if ci \<noteq> [] then
      RETURN (ci, \<sigma>\<^sub>r)
    else
      RETURN ([], False) 
  }"

lemma signed_big_int_mult_school_correct:
  assumes "(ai, a) \<in> signed_big_int_rel"
      and "(bi, b) \<in> signed_big_int_rel"
    shows "signed_big_int_mult_school ai bi \<le> \<Down> signed_big_int_rel (RETURN (a * b))"
  unfolding signed_big_int_mult_school_def
  apply (refine_vcg signed_big_int_mult_school_aux_correct'[OF assms(1) assms(2)])
  subgoal premises prems for \<sigma>\<^sub>a \<sigma>\<^sub>b r
    apply (cases \<sigma>\<^sub>a ; cases \<sigma>\<^sub>b)
    subgoal by (smt (verit, del_insts) APP_def assms(1,2) int_eq_iff minus_mult_minus
                of_nat_mult old.prod.inject prems(1,2) signed_rel_from_int_pos
                signs_rel(2))
    subgoal by (smt (verit, del_insts) APP_def assms(1,2) int_nat_eq int_ops(7)
                mult_minus_left prems(1,2,3) signed_rel_from_int_neg signs_rel(1)
                split_pairs)
    subgoal by (smt (verit, del_insts) APP_def Pair_inject assms(1,2) int_eq_iff
                int_ops(7) minus_mult_minus mult_minus_left prems(1,2,3)
                signed_rel_from_int_neg signs_rel(2) zabs_def)
    subgoal by (smt (verit, del_insts) APP_def assms(1,2) int_nat_eq int_ops(7) prems(1,2)
                prod.sel(1,2) signed_rel_from_int_pos signs_rel(1))
    done 
  subgoal for \<sigma>\<^sub>a \<sigma>\<^sub>b r
    by (simp add: signed_rel_from_int_pos)
  done

lemma signed_big_int_mult_school_refine:
  \<open>(uncurry signed_big_int_mult_school, uncurry (RETURN oo (*)))
  \<in> signed_big_int_rel \<times>\<^sub>r signed_big_int_rel \<rightarrow>\<^sub>f \<langle>signed_big_int_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
     (auto simp: uncurry_def intro!: signed_big_int_mult_school_correct)

end
