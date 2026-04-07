theory SignedBigInt
  imports BigInt
begin

text
  "We define signed big integer using a sign flag implemented by char.
  This uses more memory than GMP (which uses the sign of the length of the number)
  but it should make refinment significantly easier."
type_synonym char = "8 word"
type_synonym signed_big_int = "char \<times> big_int"

definition \<sigma> :: "signed_big_int \<Rightarrow> char" where "\<sigma> \<equiv> fst"
definition limbs_of :: "signed_big_int \<Rightarrow> big_int" where "limbs_of \<equiv> snd"

definition signed_big_int_to_int :: "signed_big_int \<Rightarrow> int" where
  "signed_big_int_to_int x = (if \<sigma> x = 0 then int (big_int_\<alpha> $ limbs_of x) else -int (big_int_\<alpha> $ limbs_of x))"

abbreviation "signed_big_int_\<alpha> \<equiv> signed_big_int_to_int"

lemma signed_big_int_zero_\<alpha>: "signed_big_int_to_int (0, []) = 0"
  by eval

definition int_to_signed_big_int :: "int \<Rightarrow> signed_big_int" where
  "int_to_signed_big_int x = (if x < 0 then (1, nat_to_big_int $ nat (abs x)) else (0, nat_to_big_int $ nat x))"

lemma signed_big_int_zero_\<gamma>: "int_to_signed_big_int 0 = (0, [])"
  by eval

text "Analogously to unsigned integers, we define a relation of signed big integers and the builtin integers.
  Note that we force the sign to be either 0 or 1 here. Also we require s = 0 for xs = [], i.e. we only allow one representation of 0."
definition "signed_big_int_invar si \<equiv> \<sigma> si = 0 \<and> limbs_of si = [] \<or> \<sigma> si < 2 \<and> limbs_of si \<noteq> [] \<and> last $ limbs_of si \<noteq> 0"

lemma sigma_impl_int_sign:
  assumes "signed_big_int_invar x"
    shows "\<sigma> x > 0 \<longleftrightarrow> signed_big_int_\<alpha> x < 0"
proof
  assume "\<sigma> x > 0"
  then have sigma_ne: "\<sigma> x \<noteq> 0" by simp
  with assms have ne: "limbs_of x \<noteq> []" and last_ne: "last (limbs_of x) \<noteq> 0"
    unfolding signed_big_int_invar_def by auto
  have "int (big_int_\<alpha> (limbs_of x)) > 0"
    using big_int_to_nat_not0[OF ne last_ne] by simp
  then show "signed_big_int_\<alpha> x < 0"
    using sigma_ne unfolding signed_big_int_to_int_def by simp
next
  assume "signed_big_int_\<alpha> x < 0"
  then have "\<sigma> x \<noteq> 0"
    unfolding signed_big_int_to_int_def by (auto split: if_splits)
  then show "\<sigma> x > 0"
    by (simp add: less_le)
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
    shows "x = (0, [])"
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
  then have "\<sigma> x = 0"
    using assms(1) unfolding signed_big_int_invar_def by auto
  then show ?thesis
    unfolding \<sigma>_def by (metis empty limbs_of_def prod.exhaust_sel)
qed

lemma signed_big_int_to_int_unique:
  assumes "signed_big_int_invar x"
      and "signed_big_int_invar x'"
      and "signed_big_int_to_int x = signed_big_int_to_int x'"
    shows "x = x'"
proof (cases "limbs_of x = [] \<and> \<sigma> x = 0")
  case True
  then have x_eq: "x = (0, [])"
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
  proof -
    have pos_iff: "(0 < \<sigma> x) = (0 < \<sigma> x')"
      using sigma_impl_int_sign[OF assms(1)] sigma_impl_int_sign[OF assms(2)] assms(3)
      by simp
    have lt2_x: "unat (\<sigma> x) < 2"
      using assms(1) x_ne unfolding signed_big_int_invar_def
      by (auto simp: word_less_nat_alt)
    have lt2_x': "unat (\<sigma> x') < 2"
      using assms(2) unfolding signed_big_int_invar_def
      by (auto simp: word_less_nat_alt)
    have nat_iff: "(0 < unat (\<sigma> x)) = (0 < unat (\<sigma> x'))"
      using pos_iff by (simp add: word_less_nat_alt)
    have "unat (\<sigma> x) = unat (\<sigma> x')"
      using lt2_x lt2_x' nat_iff by linarith
    thus ?thesis
      by (simp add: word_unat.Rep_inject)
  qed
  have alpha_eq: "big_int_\<alpha> (limbs_of x) = big_int_\<alpha> (limbs_of x')"
    using assms(3) sign_eq unfolding signed_big_int_to_int_def by (auto split: if_splits)
  have uinvar_x: "big_int_invar (limbs_of x)"
    by (rule signed_big_int_invar_impl_unsigned_invar[OF assms(1)])
  have uinvar_x': "big_int_invar (limbs_of x')"
    by (rule signed_big_int_invar_impl_unsigned_invar[OF assms(2)])
  have limbs_eq: "limbs_of x = limbs_of x'"
    using big_int_to_nat_unique uinvar_x uinvar_x' alpha_eq by blast
  show ?thesis
    by (metis \<sigma>_def limbs_eq limbs_of_def prod.collapse sign_eq)
qed
  
definition "signed_big_int_rel \<equiv> br signed_big_int_to_int signed_big_int_invar"

text "We can show that the signed big int relation generalizes the unsigned variant."

definition \<sigma>_int :: "signed_big_int \<Rightarrow> int" where
  "\<sigma>_int x = (if \<sigma> x = 0 then 1 else -1)"

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
    by (metis \<sigma>_def assms(5) limbs_eq limbs_of_def prod.collapse)
qed

lemma cases_sign:
  assumes "signed_big_int_invar xi"
    shows "\<sigma> xi = 0 \<or> \<sigma> xi = 1"
by (metis arith_special(3) assms inc_le less_le signed_big_int_invar_def verit_comp_simplify(3) word_less_1)

lemma signs_rel:
  assumes "(ai, a) \<in> signed_big_int_rel"
    shows "\<sigma> ai = 0 \<longleftrightarrow> a \<ge> 0"
      and "\<sigma> ai = 1 \<longleftrightarrow> a < 0"
  apply (smt (verit) assms in_br_conv sigma_impl_int_sign signed_big_int_rel_def word_greater_zero_iff)
  apply (metis assms signed_big_int_rel_def in_br_conv cases_sign sigma_impl_int_sign word_less_1 word_gt_0)
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
    shows "((0,ai),a) \<in> signed_big_int_rel"
proof -
  have "signed_big_int_\<alpha> (0,ai) = int $ big_int_\<alpha> ai"
    unfolding signed_big_int_to_int_def \<sigma>_def limbs_of_def by simp
  then have val: "signed_big_int_\<alpha> (0,ai) = a"
    using assms by simp
  have "last ai \<noteq> 0 \<or> ai = []"
    using assms(2) big_int_invar_def by auto
  then have "signed_big_int_invar (0,ai)"
    unfolding signed_big_int_invar_def \<sigma>_def limbs_of_def by auto
  then show ?thesis
    by (simp add: brI signed_big_int_rel_def val)
qed 

lemma signed_rel_from_int_neg:
  assumes "int $ big_int_\<alpha> ai = a"
      and "big_int_invar ai"
      and "ai \<noteq> []"
    shows "((1,ai),-a) \<in> signed_big_int_rel"
proof -
  have "signed_big_int_\<alpha> (1,ai) = -int $ big_int_\<alpha> ai"
    unfolding signed_big_int_to_int_def \<sigma>_def limbs_of_def by simp
  then have val: "signed_big_int_\<alpha> (1,ai) = -a"
    using assms by simp
  have "signed_big_int_invar (1,ai)"
    unfolding signed_big_int_invar_def \<sigma>_def limbs_of_def
    using assms(2) assms(3)
    unfolding big_int_invar_def
    by auto
  then show ?thesis
    by (simp add: brI signed_big_int_rel_def val)
qed    

section "Arithmetic Operations"

subsection "Addition"
text "We can consider two cases: The signs of the inputs are equal, or they are not."

definition signed_big_int_add_\<sigma>_eq :: "signed_big_int \<Rightarrow> signed_big_int \<Rightarrow> signed_big_int nres" where
  "signed_big_int_add_\<sigma>_eq ai bi = doN {
    let (\<sigma>\<^sub>a, \<sigma>\<^sub>b) = (\<sigma> ai, \<sigma> bi);
    ASSERT(\<sigma>\<^sub>a = \<sigma>\<^sub>b);
    ri \<leftarrow> big_int_add (limbs_of ai) (limbs_of bi);
    RETURN(\<sigma>\<^sub>a, ri) 
  }"

lemma signed_big_int_add_\<sigma>_eq_correct:
  assumes "(ai, a) \<in> signed_big_int_rel"
      and "(bi, b) \<in> signed_big_int_rel"
      and "\<sigma> ai = \<sigma> bi"
    shows "signed_big_int_add_\<sigma>_eq ai bi \<le> \<Down>signed_big_int_rel (RETURN (a + b))"
proof -
  have invar_ai: "signed_big_int_invar ai" and a_val: "a = signed_big_int_to_int ai"
    using assms(1) unfolding signed_big_int_rel_def in_br_conv by simp_all
  have invar_bi: "signed_big_int_invar bi" and b_val: "b = signed_big_int_to_int bi"
    using assms(2) unfolding signed_big_int_rel_def in_br_conv by simp_all
  let ?na = "big_int_\<alpha> (limbs_of ai)"
  let ?nb = "big_int_\<alpha> (limbs_of bi)"
  have rel_ai: "(limbs_of ai, ?na) \<in> big_int_rel"
    using signed_big_int_invar_impl_unsigned_invar[OF invar_ai]
    unfolding big_int_rel_def in_br_conv by simp
  have rel_bi: "(limbs_of bi, ?nb) \<in> big_int_rel"
    using signed_big_int_invar_impl_unsigned_invar[OF invar_bi]
    unfolding big_int_rel_def in_br_conv by simp
  show ?thesis
    unfolding signed_big_int_add_\<sigma>_eq_def 
    apply (refine_vcg big_int_add_correct'[OF rel_ai rel_bi])
    subgoal by (auto simp: assms(3))
    subgoal premises prems for \<sigma>\<^sub>a \<sigma>\<^sub>b r
    proof -
      have h_\<sigma>a: "\<sigma>\<^sub>a = \<sigma> ai" using prems(1) by simp
      have h_r_val: "big_int_\<alpha> r = big_int_\<alpha> (limbs_of ai) + big_int_\<alpha> (limbs_of bi)"
        using prems(3) unfolding big_int_rel_def in_br_conv by simp
      have h_r_invar: "big_int_invar r"
        using prems(3) unfolding big_int_rel_def in_br_conv by simp
      have hinvar: "signed_big_int_invar (\<sigma>\<^sub>a, r)"
        unfolding signed_big_int_invar_def \<sigma>_def limbs_of_def
        using h_\<sigma>a h_r_invar h_r_val invar_ai signed_big_int_invar_impl_unsigned_invar[OF invar_ai]
        unfolding signed_big_int_invar_def big_int_invar_def
        by (auto simp: word_less_nat_alt dest: big_int_to_nat_not0)
      have hval: "signed_big_int_to_int (\<sigma>\<^sub>a, r) = a + b"
        using h_\<sigma>a h_r_val a_val b_val assms(3)
        by (simp add: int_of_signed_big_int_alt \<sigma>_int_def \<sigma>_def limbs_of_def ring_distribs)
      show ?thesis
        unfolding signed_big_int_rel_def in_br_conv
        using hinvar hval by simp
    qed
    done 
qed

definition signed_big_int_add_\<sigma>_neq :: "signed_big_int \<Rightarrow> signed_big_int \<Rightarrow> signed_big_int nres" where
  "signed_big_int_add_\<sigma>_neq ai bi = doN {
    let (\<sigma>\<^sub>a, \<sigma>\<^sub>b) = (\<sigma> ai, \<sigma> bi);
    ASSERT(\<sigma>\<^sub>a \<noteq> \<sigma>\<^sub>b);
    let pos_l = (if \<sigma>\<^sub>a = 0 then limbs_of ai else limbs_of bi);
    let neg_l = (if \<sigma>\<^sub>a = 0 then limbs_of bi else limbs_of ai);
    pos_lt \<leftarrow> big_int_lt pos_l neg_l;
    if pos_lt then do {
      (ci, _) \<leftarrow> big_int_sub neg_l pos_l;
      RETURN (1, ci)
    } else do {
      (ci, _) \<leftarrow> big_int_sub pos_l neg_l;
      RETURN (0, ci)
    }
  }"

lemma word_aux:
  assumes "(x::8 word) \<noteq> 0"
  and "x < 2"
  shows "x = 1"
  by (metis assms(1,2) div_less_dividend_word div_word_self inc_le one_add_one verit_comp_simplify1(3))

lemma big_int_lt_correct': "(ai, a) \<in> big_int_rel \<Longrightarrow> (bi, b) \<in> big_int_rel \<Longrightarrow> big_int_lt ai bi \<le> SPEC (\<lambda> ci. (ci, a < b) \<in> bool_rel)" 
  using big_int_lt_correct
  by (metis conc_fun_RETURN)

lemma signed_big_int_add_\<sigma>_neq_correct:
  assumes "(ai, a) \<in> signed_big_int_rel"
      and "(bi, b) \<in> signed_big_int_rel"
      and "\<sigma> ai \<noteq> \<sigma> bi"
  shows "signed_big_int_add_\<sigma>_neq ai bi \<le> \<Down>signed_big_int_rel (RETURN (a + b))"
proof -
  have invar_ai: "signed_big_int_invar ai" and a_val: "a = signed_big_int_to_int ai"
    using assms(1) unfolding signed_big_int_rel_def in_br_conv by simp_all
  have invar_bi: "signed_big_int_invar bi" and b_val: "b = signed_big_int_to_int bi"
    using assms(2) unfolding signed_big_int_rel_def in_br_conv by simp_all
  have abs_rel_ai: "(limbs_of ai, nat $ abs a) \<in> big_int_rel"
    using abs_rel assms(1) by blast
  have abs_rel_bi: "(limbs_of bi, nat $ abs b) \<in> big_int_rel"
    using abs_rel assms(2) by blast
  show ?thesis proof (cases "\<sigma> ai = 0")
    case True
    then have \<sigma>_ai_eq_zero: "\<sigma> ai = 0"
      by simp
    then have \<sigma>_bi_eq_one: "\<sigma> bi = 1"
      using invar_bi assms(3)
      unfolding signed_big_int_invar_def
      by (auto simp: word_aux)
    have \<sigma>_a: "a \<ge> 0"
      using \<sigma>_ai_eq_zero assms(1) signs_rel(1) by blast
    have \<sigma>_b: "b < 0"
      using \<sigma>_bi_eq_one assms(2) signs_rel(2) by blast
    then show ?thesis
    proof (cases "big_int_\<alpha> (limbs_of ai) < big_int_\<alpha> (limbs_of bi)") 
      case True
      then have a_lt_b: "abs a < abs b"
        by (metis APP_def \<sigma>_a \<sigma>_ai_eq_zero a_val abs_from_limbs abs_of_nonneg assms(2) signed_big_int_to_int_def zless_nat_eq_int_zless)
      then have add_by_sub: "a + b = - (abs b - abs a)"
        using \<sigma>_a \<sigma>_b by force
      then show ?thesis 
      unfolding signed_big_int_add_\<sigma>_neq_def add_by_sub
      apply (auto simp: \<sigma>_ai_eq_zero)
      apply (refine_vcg big_int_lt_correct'[OF abs_rel_ai abs_rel_bi]
                        big_int_sub_correct[OF abs_rel_ai abs_rel_bi]
                        big_int_sub_correct[OF abs_rel_bi abs_rel_ai])
      subgoal using \<sigma>_bi_eq_one by simp 
      subgoal premises prems for lt tup rs zero_
      proof -
        have inv_rs: "big_int_invar rs"
          by (metis (mono_tags, lifting) True abs_rel_ai abs_rel_bi big_int_rel_def
              in_br_conv le_eq_less_or_eq linorder_not_le old.prod.case prems(4,5))
        have rs_neq_zero: "rs \<noteq> []"
          by (smt (verit, best) True abs_rel_ai abs_rel_bi big_int_\<alpha>_unwrap
              big_int_to_nat.simps(1) diff_is_0_eq le_eq_less_or_eq linorder_not_le old.prod.case prems(4,5))
        have "(rs, nat $ abs b - nat $ abs a) \<in> big_int_rel"
          using prems by auto 
        then have "big_int_\<alpha> rs = nat $ abs b - nat $ abs a"
          using big_int_\<alpha>_unwrap by blast
        then have "int $ big_int_\<alpha> rs = abs b - abs a"
          using a_lt_b by (simp add: \<sigma>_ai_eq_zero a_val b_val prems(1) signed_big_int_to_int_def)
        then have "-int $ big_int_\<alpha> rs = abs a - abs b"
          by algebra
        then have "int $ big_int_\<alpha> rs = -(abs a - abs b)"
          by algebra
        then show ?thesis
          using inv_rs rs_neq_zero signed_rel_from_int_neg by fastforce
      qed 
      subgoal using a_lt_b by auto
      done
    next
      case False
      then have b_lt_a: "abs b \<le> abs a"
        using abs_rel_ai abs_rel_bi
        by (metis APP_def \<sigma>_a abs_of_nonneg big_int_\<alpha>_unwrap int_eq_iff linorder_not_le nat_le_iff)
      then have add_by_sub: "a + b = abs a - abs b"
        using \<sigma>_a \<sigma>_b by force
      then show ?thesis 
      unfolding signed_big_int_add_\<sigma>_neq_def add_by_sub
      apply (auto simp: \<sigma>_ai_eq_zero)
      apply (refine_vcg big_int_lt_correct'[OF abs_rel_ai abs_rel_bi]
                        big_int_sub_correct[OF abs_rel_ai abs_rel_bi]
                        big_int_sub_correct[OF abs_rel_bi abs_rel_ai])
      subgoal using \<sigma>_bi_eq_one by simp 
      subgoal using b_lt_a by auto 
      subgoal premises prems for lt tup rs zero_
        thm prems
      proof -
        have inv_rs: "big_int_invar rs"
          by (metis (mono_tags, lifting) False abs_rel_ai abs_rel_bi big_int_rel_def
             case_prod_unfold in_br_conv prems(4,5) prod.sel(1))
        have "(rs, nat $ abs a - nat $ abs b) \<in> big_int_rel"
          using prems by auto 
        then have "big_int_\<alpha> rs = nat $ abs a - nat $ abs b"
          using big_int_\<alpha>_unwrap by blast
        then have "int $ big_int_\<alpha> rs = abs a - abs b"
          using b_lt_a by (simp add: \<sigma>_ai_eq_zero a_val b_val prems(1) signed_big_int_to_int_def)
        then show ?thesis
          using inv_rs signed_rel_from_int_pos by fastforce
      qed 
      done
    qed
  next
    case False
    then have \<sigma>_ai_eq_one: "\<sigma> ai = 1"
      using invar_ai
      unfolding signed_big_int_invar_def
      by (auto simp: word_aux)
    then have \<sigma>_bi_eq_zero: "\<sigma> bi = 0"
      using invar_bi assms(3)
      unfolding signed_big_int_invar_def
      by (metis word_aux)
    have \<sigma>_a: "a < 0"
      using \<sigma>_ai_eq_one assms(1) signs_rel(2) by blast
    have \<sigma>_b: "b \<ge> 0"
      using \<sigma>_bi_eq_zero assms(2) signs_rel(1) by blast
    then show ?thesis
    proof (cases "big_int_\<alpha> (limbs_of bi) < big_int_\<alpha> (limbs_of ai)")
      case True
      then have b_lt_a: "abs b < abs a"
        by (metis APP_def \<sigma>_b \<sigma>_bi_eq_zero b_val abs_from_limbs abs_of_nonneg assms(1) signed_big_int_to_int_def zless_nat_eq_int_zless)
      then have add_by_sub: "a + b = -(abs a - abs b)"
        using \<sigma>_a \<sigma>_b by force
      then show ?thesis
      unfolding signed_big_int_add_\<sigma>_neq_def add_by_sub
      apply (auto simp: \<sigma>_ai_eq_one)
      apply (refine_vcg big_int_lt_correct'[OF abs_rel_bi abs_rel_ai]
                        big_int_sub_correct[OF abs_rel_ai abs_rel_bi]
                        big_int_sub_correct[OF abs_rel_bi abs_rel_ai])
      subgoal using \<sigma>_bi_eq_zero by simp
      subgoal premises prems for lt tup rs zero_
      proof -
        have inv_rs: "big_int_invar rs"
          by (metis (mono_tags, lifting) True abs_rel_ai abs_rel_bi big_int_rel_def
              in_br_conv le_eq_less_or_eq linorder_not_le old.prod.case prems(4,5))
        have rs_neq_zero: "rs \<noteq> []"
          by (smt (verit, best) True abs_rel_ai abs_rel_bi big_int_\<alpha>_unwrap
              big_int_to_nat.simps(1) diff_is_0_eq le_eq_less_or_eq linorder_not_le old.prod.case prems(4,5))
        have "(rs, nat $ abs a - nat $ abs b) \<in> big_int_rel"
          using prems by auto
        then have "big_int_\<alpha> rs = nat $ abs a - nat $ abs b"
          using big_int_\<alpha>_unwrap by blast
        then have "int $ big_int_\<alpha> rs = abs a - abs b"
          using b_lt_a by (simp add: \<sigma>_ai_eq_one a_val b_val prems(1) signed_big_int_to_int_def)
        then have "-int $ big_int_\<alpha> rs = abs b - abs a"
          by algebra
        then have "int $ big_int_\<alpha> rs = -(abs b - abs a)"
          by algebra
        then show ?thesis
          using inv_rs rs_neq_zero signed_rel_from_int_neg by fastforce
      qed
      subgoal using b_lt_a by auto
      done
    next
      case False
      then have a_lt_b: "abs a \<le> abs b"
        using abs_rel_ai abs_rel_bi
        by (metis APP_def \<sigma>_b abs_of_nonneg big_int_\<alpha>_unwrap int_eq_iff linorder_not_le nat_le_iff)
      then have add_by_sub: "a + b = abs b - abs a"
        using \<sigma>_a \<sigma>_b by force
      then show ?thesis
      unfolding signed_big_int_add_\<sigma>_neq_def add_by_sub
      apply (auto simp: \<sigma>_ai_eq_one)
      apply (refine_vcg big_int_lt_correct'[OF abs_rel_bi abs_rel_ai]
                        big_int_sub_correct[OF abs_rel_ai abs_rel_bi]
                        big_int_sub_correct[OF abs_rel_bi abs_rel_ai])
      subgoal using \<sigma>_bi_eq_zero by simp
      subgoal using a_lt_b by auto
      subgoal premises prems for lt tup rs zero_
      proof -
        have inv_rs: "big_int_invar rs"
          by (metis (mono_tags, lifting) False abs_rel_ai abs_rel_bi big_int_rel_def
             case_prod_unfold in_br_conv prems(4,5) prod.sel(1))
        have "(rs, nat $ abs b - nat $ abs a) \<in> big_int_rel"
          using prems by auto
        then have "big_int_\<alpha> rs = nat $ abs b - nat $ abs a"
          using big_int_\<alpha>_unwrap by blast
        then have "int $ big_int_\<alpha> rs = abs b - abs a"
          using a_lt_b by (simp add: \<sigma>_ai_eq_one a_val b_val prems(1) signed_big_int_to_int_def)
        then show ?thesis
          using inv_rs signed_rel_from_int_pos by fastforce
      qed
      done
    qed
  qed
qed

definition signed_big_int_add :: "signed_big_int \<Rightarrow> signed_big_int \<Rightarrow> signed_big_int nres" where
  "signed_big_int_add ai bi = do {
    let (\<sigma>\<^sub>a, \<sigma>\<^sub>b) = (\<sigma> ai, \<sigma> bi);
    if \<sigma>\<^sub>a = \<sigma>\<^sub>b then do {
      ci \<leftarrow> big_int_add (limbs_of ai) (limbs_of bi);
      RETURN (\<sigma>\<^sub>a, ci)
    } else do {
      let pos_l = (if \<sigma>\<^sub>a = 0 then limbs_of ai else limbs_of bi);
      let neg_l = (if \<sigma>\<^sub>a = 0 then limbs_of bi else limbs_of ai);
      pos_lt \<leftarrow> big_int_lt pos_l neg_l;
      if pos_lt then do {
        (ci, _) \<leftarrow> big_int_sub neg_l pos_l;
        RETURN (1, ci)
      } else do {
        (ci, _) \<leftarrow> big_int_sub pos_l neg_l;
        RETURN (0, ci)
      }
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

end
