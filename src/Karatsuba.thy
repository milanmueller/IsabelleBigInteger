theory Karatsuba
  imports Setup BigInt AuxLemmas
begin 

subsection \<open>Karatsuba Algorithm\<close>

lemma karatsuba_split_formula_nat:
	fixes a b :: nat
	assumes "a = a\<^sub>l*B + a\<^sub>r"	
	assumes "b = b\<^sub>l*B + b\<^sub>r"	
	assumes "z\<^sub>0 = a\<^sub>r*b\<^sub>r"
	assumes "z\<^sub>1 = (a\<^sub>l+a\<^sub>r)*(b\<^sub>l+b\<^sub>r)"
	assumes "z\<^sub>2 = a\<^sub>l*b\<^sub>l"
	shows "a*b = z\<^sub>2*B^2 + (z\<^sub>1-(z\<^sub>2+z\<^sub>0))*B + z\<^sub>0"
	unfolding assms
	by (auto simp: algebra_simps power2_eq_square)
	

lemma karatsuba_split_formula_nat':
	fixes a b :: nat
	assumes BN: "B\<noteq>0"
	assumes A: "a\<^sub>l = a div B" "a\<^sub>r = a mod B"
	assumes B: "b\<^sub>l = b div B" "b\<^sub>r = b mod B"
	assumes "z\<^sub>0 = a\<^sub>r*b\<^sub>r"
	assumes "z\<^sub>1 = (a\<^sub>l+a\<^sub>r)*(b\<^sub>l+b\<^sub>r)"
	assumes "z\<^sub>2 = a\<^sub>l*b\<^sub>l"
	shows "a*b = z\<^sub>2*B^2 + (z\<^sub>1-(z\<^sub>2+z\<^sub>0))*B + z\<^sub>0"
	apply (rule karatsuba_split_formula_nat; fact?)
	unfolding A B using BN by auto
	
definition karatsuba_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat nres" 
where "karatsuba_nat a b \<equiv> RECT (\<lambda> karatsuba (a, b). do {
	if a=0 then RETURN 0
	else if b=0 then RETURN 0
	else if a<limb_sz then RETURN (b*a)
	else if b<limb_sz then RETURN (a*b)
	else do {
		let la = size_log a;
		let lb = size_log b;
		let m = min la lb div 2;
		let B = limb_sz^m;
		let a\<^sub>r = a mod B;
		let a\<^sub>l = a div B;
		let b\<^sub>r = b mod B;
		let b\<^sub>l = b div B;
		
		let a_sum = a\<^sub>l+a\<^sub>r;
		let b_sum = b\<^sub>l+b\<^sub>r;
		
		z\<^sub>2 \<leftarrow> karatsuba (a\<^sub>l,b\<^sub>l);
		z\<^sub>0 \<leftarrow> karatsuba (a\<^sub>r,b\<^sub>r);
		
		let z_sum = z\<^sub>2+z\<^sub>0;
		z\<^sub>1 \<leftarrow> karatsuba (a_sum,b_sum);
		ASSERT(z\<^sub>1 \<ge> z_sum);
		let t\<^sub>1 = z\<^sub>1 - z_sum;
		let t\<^sub>1 = t\<^sub>1*B;
		let t\<^sub>1 = t\<^sub>1 + z\<^sub>0;
		
		let t\<^sub>2 = z\<^sub>2 * B^2;
		
		RETURN (t\<^sub>1+t\<^sub>2)
	}
}) (a,b)"	

lemma size_log_max: "min (size_log a) (size_log b) = size_log (min a b)"
	unfolding size_log_def limb_sz_unfold
	by (metis floorlog_mono min_def nle_le limb_sz_unfold)

lemma size_log_div2_aux: "a \<ge> limb_sz \<Longrightarrow>  limb_sz ^ (size_log a div 2) \<le> a"
proof -
	assume A_GT: "a \<ge> limb_sz"
	hence "size_log a \<ge> 2" using size_log_def compute_floorlog
		by (metis floorlog_mono nat_1_add_1 power_one_right size_log_pow)
	hence "size_log a div 2 \<le> size_log a - 1" by auto
	hence 1: "limb_sz ^ (size_log a div 2) \<le> limb_sz ^ (size_log a - 1)" 
		using limb_sz_gt power_increasing_iff by blast

	have "limb_sz ^ (floorlog limb_sz a - 1) \<le> a" 
		using floorlog_bounds[of a limb_sz] A_GT limb_sz_gt by linarith
	thus ?thesis using 1 using size_log_def by auto
qed


lemma karatsuba_nat_correct': "karatsuba_nat a b \<le> RETURN (a*b)"
proof -

	define e where "e = (\<lambda>a b. limb_sz ^ (min (size_log a) (size_log b) div 2))"
	note E = e_def[symmetric, THEN fun_cong, THEN fun_cong]

	have E_NZ[simp]: "e a b \<noteq> 0" for a b
		unfolding e_def by (simp add: limb_sz_def)

	have E_GT2: "e a b > 2" if "limb_sz \<le> a" "limb_sz \<le> b" for a b
	proof -
		from that
		have "size_log a \<ge> 2 \<and> size_log b \<ge> 2"
			using size_log_def compute_floorlog
			by (metis floorlog_mono nat_1_add_1 power_one_right size_log_pow)
		hence "min (size_log a) (size_log b) div 2 \<ge> 1"
			by auto
		hence "e a b \<ge> limb_sz" using E[of a b]
			using power_increasing[of 1 "min (size_log a) (size_log b) div 2" limb_sz]
			by (metis one_le_numeral one_le_power power_one_right limb_sz_unfold)
			
		thus ?thesis
			unfolding e_def using limb_sz_gt
			by linarith
	qed    

	have E_LT: "e a b \<le> min a b" if AB_LT: "limb_sz \<le> a" "limb_sz \<le> b" for a b 
		unfolding e_def using AB_LT size_log_max size_log_div2_aux[of "min a b"] 
		by presburger
	
	show ?thesis
		unfolding karatsuba_nat_def
		supply R = RECT_rule[where pre=top and V="measure (\<lambda>(a,b). a+b)" and M="\<lambda>(a,b). SPEC (\<lambda>r::nat. r=a*b)"]
	
		apply (refine_vcg R[THEN order_trans])
		apply (all \<open>(thin_tac "RECT _ = _")?\<close>)
		unfolding E
		
		apply (all \<open>(simp; fail)?\<close>)
		
		apply (rule order_trans)
		apply rprems
		apply (simp; fail)
		
		apply clarsimp
		subgoal for a b
			using E_GT2[of a b]
			by (simp add: add_less_mono)
		apply refine_vcg
		
		apply (rule order_trans)
		apply rprems
		apply (simp; fail)
		
		apply clarsimp
		subgoal for a b proof -
			assume "0 < a" "0 < b" "\<not> a < limb_sz" "\<not> b < limb_sz"
			hence "a \<ge> limb_sz" "b \<ge> limb_sz" by auto
			hence "e a b \<le> max a b" using E_LT[of a b] by auto
			hence "(max a b) mod e a b < (max a b)"
				by (meson E_NZ dual_order.strict_trans1 mod_less_divisor not_gr_zero)
			hence "a mod e a b < a \<or> b mod e a b < b"
				by linarith
			thus ?thesis 
				by (meson add_less_le_mono add_mono_thms_linordered_field(4) mod_less_eq_dividend)
		qed
			
		apply refine_vcg
		
		apply (rule order_trans)
		apply rprems
		apply (simp; fail)
		
		apply clarsimp
		subgoal for a b proof -
			assume "0 < a" "0 < b" "\<not> a < limb_sz" "\<not> b < limb_sz"
			hence AB_GT: "a \<ge> limb_sz" "b \<ge> limb_sz" by auto
			define ab_min ab_max where ab_def: "ab_min = min a b" "ab_max = max a b"

			have "a div e a b + a mod e a b + (b div e a b + b mod e a b) = 
				ab_min div e a b + ab_min mod e a b + ab_max div e a b + ab_max mod e a b" using ab_def by auto
			 
			have ab_min: "ab_min div e a b + ab_min mod e a b \<le> ab_min" using mod_div_less[of ab_min "e a b"] by auto
			have 1: "e a b \<le> ab_max" using ab_def E_LT[of a b] AB_GT by auto
			have 2: "e a b > 2" using E_GT2[of a b] AB_GT by auto
			hence ab_max: "ab_max div e a b + ab_max mod e a b < ab_max" 
				using mod_div_less_strict[of "e a b" ab_max] 1 2 by presburger

			thus ?thesis using ab_min ab_max ab_def
				by (metis add.commute add_less_le_mono max_def mod_div_less)
		qed
	
		apply refine_vcg
		
		apply clarsimp_all
		subgoal for karatsuba a b by (simp add: algebra_simps)
		subgoal for karatsuba a b
			apply (subgoal_tac "e a b \<noteq> 0")
			subgoal
				using karatsuba_split_formula_nat'[where B="e a b" and a=a and b=b, OF _ refl refl refl refl refl refl refl]
				by (simp add: algebra_simps)
			by simp
		done
qed    

definition big_int_eq :: "big_int \<Rightarrow> big_int \<Rightarrow> bool nres" where "
  big_int_eq xs ys \<equiv> do {
    
    let xl = big_int_length xs;
    let yl = big_int_length ys;
    if xl \<noteq> yl then RETURN False
    else do {
      (idx, res) \<leftarrow> WHILEIT
          (\<lambda> (idx, res). res = (take idx xs = take idx ys))
          (\<lambda> (idx, res). res \<and> idx < xl)
          (\<lambda> (idx, res). do {
            
            ASSUME (sepref_sorry_that(length xs+1 < max_snat 64));
            ASSERT (idx + 1 < max_snat 64);

            let xidx = get_or_zero xs idx;
            let yidx = get_or_zero ys idx;
            let idx = idx + 1;
            if xidx = yidx 
              then RETURN (idx, res)
              else RETURN (idx, False)
          })
          (0, True);
      RETURN res
    }
}"

lemma big_int_eq_correct[simp]: "(ai, a) \<in> big_int_rel \<Longrightarrow> (bi, b) \<in> big_int_rel \<Longrightarrow> big_int_eq ai bi \<le> (RETURN (a = b))"
	unfolding big_int_eq_def big_int_rel_def in_br_conv
  apply (refine_vcg WHILEIT_rule[where R="measure (\<lambda> (idx, _). length ai - idx)"])
  subgoal using big_int_to_nat_unique by blast
  subgoal by fastforce
  subgoal by fastforce
  subgoal using sepref_sorry by auto
  apply clarsimp
  subgoal for idx s s' proof (cases "idx < big_int_length ai")
    assume eql: "big_int_length ai = big_int_length bi"
    case True
    hence takea: "take (Suc idx) ai = (take idx ai) @ [get_or_zero ai idx]"
      by (simp add: big_int_length_def get_or_zero_def take_Suc_conv_app_nth)
    have takeb: "take (Suc idx) bi = (take idx bi) @ [get_or_zero bi idx]" using True eql
      by (simp add: big_int_length_def get_or_zero_def take_Suc_conv_app_nth)

    assume "get_or_zero ai idx = get_or_zero bi idx" "take idx ai = take idx bi"
    then show ?thesis using takea takeb by presburger
  next
    assume eql: "big_int_length ai = big_int_length bi"
    case False
    hence takea: "take (Suc idx) ai = (take idx ai)"
      by (simp add: big_int_length_def)
    have takeb: "take (Suc idx) bi = (take idx bi)" using False eql
      by (simp add: big_int_length_def)

    assume  "take idx ai = take idx bi"
    then show ?thesis using takea takeb by simp
  qed
  apply clarsimp
  subgoal using big_int_length_def by auto
    apply clarsimp
  subgoal for idx s s' proof -
    assume eql: "big_int_length ai = big_int_length bi"
    assume idx: "idx < big_int_length bi"

    have takeb: "take (Suc idx) bi = (take idx bi) @ [get_or_zero bi idx]"
      using idx
      by (simp add: big_int_length_def get_or_zero_def take_Suc_conv_app_nth)

    have takea: "take (Suc idx) ai = (take idx ai) @ [get_or_zero ai idx]"
      using eql idx
      by (simp add: big_int_length_def get_or_zero_def take_Suc_conv_app_nth)

    assume neq: "get_or_zero ai idx \<noteq> get_or_zero bi idx"
    assume "take (Suc idx) ai = take (Suc idx) bi"
    hence "get_or_zero bi idx = get_or_zero ai idx" using takea takeb by auto
    thus ?thesis using neq by simp
  qed
   apply clarsimp
  subgoal unfolding big_int_length_def
    by linarith
  apply clarsimp
  by (metis big_int_length_def leI nat_to_big_int_inv take_all)
  
lemma big_int_length_zero_rel: "(ai, a) \<in> big_int_rel \<Longrightarrow> (big_int_length ai = 0 \<longleftrightarrow> a = 0)"
  using big_int_length_def big_int_length_pow_gt big_int_rel_length_log by fastforce

lemma big_int_length_zero_rel': "(ai, a) \<in> big_int_rel \<Longrightarrow> (length ai = 0) = (a = 0)"
  using big_int_length_zero_rel unfolding big_int_length_def by simp

definition big_int_mult_small :: "big_int \<Rightarrow> big_int \<Rightarrow> big_int nres"
  where "big_int_mult_small ai bi \<equiv> do {
    ASSERT (length ai = 1);
    ail \<leftarrow> big_int_small_to_limb ai;
    res \<leftarrow> big_int_mult_limb bi ail;
    RETURN res
}"

lemma big_int_mult_small_correct:
  "(ai, a) \<in> big_int_rel \<Longrightarrow> (bi, b) \<in> big_int_rel \<Longrightarrow>
  length ai = 1 \<Longrightarrow> a < limb_sz \<Longrightarrow> big_int_mult_small ai bi \<le> \<Down> big_int_rel (Refine_Basic.RETURN (b * a))"
  unfolding big_int_mult_small_def 
  apply (refine_vcg big_int_limb_aux_correct big_int_trim_correct big_int_mult_limb_correct'
        big_int_small_to_limb_correct)
  apply assumption
  subgoal using big_int_rel_bounds 
    by (metis big_int_length_zero_rel' not_one_less_zero zero_less_one)
  apply simp
  apply assumption
  apply blast
  by meson


(* Karatsuba base cases *)
definition karatsuba_RECT_base
  where "karatsuba_RECT_base recurse \<equiv> do {
  RECT (\<lambda> kara (ai, bi). do {
          if length ai = 0 then RETURN big_int0
    else  if length bi = 0 then RETURN big_int0
    else  if length ai = 1 then big_int_mult_small ai bi
    else  if length bi = 1 then big_int_mult_small bi ai
    else  recurse ai bi kara
  })
}"

definition karatsuba_aux :: "big_int \<Rightarrow> big_int
  \<Rightarrow> (nat \<Rightarrow> big_int \<Rightarrow> big_int \<Rightarrow> big_int \<Rightarrow> big_int \<Rightarrow> big_int nres)
  \<Rightarrow> big_int nres"
  where "karatsuba_aux ai bi p \<equiv> do {
    ASSERT (length ai \<ge> 2);
    ASSERT (length bi \<ge> 2);
    let la = length ai;
    let lb = length bi;
    let m = min la lb div 2; \<comment> \<open>find midpoint: B = limb_sz ^ m \<close>
    ai_right \<leftarrow> big_int_take m ai;
    ai_left  \<leftarrow> big_int_drop m ai; \<comment> \<open>a = a_left * B + a_right\<close>

    bi_right \<leftarrow> big_int_take m bi;
    bi_left  \<leftarrow> big_int_drop m bi; \<comment> \<open>b = b_left * B + b_right\<close>
    
    res \<leftarrow> p m ai_left ai_right bi_left bi_right;

    RETURN res
}"

(* Recursive step of karatsuba *)
definition karatsuba_recurse :: "((big_int \<times> big_int) \<Rightarrow> big_int nres) \<Rightarrow>
  nat \<Rightarrow> big_int \<Rightarrow> big_int \<Rightarrow> big_int \<Rightarrow> big_int \<Rightarrow> big_int nres"
  where "karatsuba_recurse kara m ai_left ai_right bi_left bi_right \<equiv> do {
			ai_sum \<leftarrow> big_int_add ai_left ai_right;
			bi_sum \<leftarrow> big_int_add bi_left bi_right;

			z_2 \<leftarrow> kara (ai_left, bi_left);

			z_0 \<leftarrow> kara (ai_right, bi_right);
			z_sum \<leftarrow> big_int_add z_2 z_0;

			z_3 \<leftarrow> kara (ai_sum, bi_sum);

			z_1 \<leftarrow> big_int_sub_compl z_3 z_sum;

			z_1 \<leftarrow> big_int_rshift m z_1;

			aux \<leftarrow> big_int_add z_1 z_0;
			z_2 \<leftarrow> big_int_rshift (2*m) z_2;

			res \<leftarrow> big_int_add aux z_2;

      RETURN res
}"

definition karatsuba :: "big_int \<Rightarrow> big_int \<Rightarrow> big_int nres"
  where "karatsuba ai bi \<equiv> karatsuba_RECT_base
  (\<lambda> ai bi kara. karatsuba_aux ai bi (karatsuba_recurse kara))
  (ai, bi)"

thm "top_nres_def"

lemmas [refine_dref_RELATES] = RELATESI[of big_int_rel]

lemmas [refine] = big_int_drop_correct_eq big_int_take_correct_eq big_int_add_correct big_int_sub_compl_correct 
		big_int_rshift_correct_sqr big_int_rshift_correct_eq big_int_eq_correct big_int_mult_limb_correct

find_theorems "bind" "RETURN"

lemma karatsuba_refine:
	assumes "(ai, a) \<in> big_int_rel" "(bi, b) \<in> big_int_rel"
	shows "karatsuba ai bi \<le>\<Down>big_int_rel (karatsuba_nat a b)"	
	unfolding karatsuba_def karatsuba_RECT_base_def karatsuba_recurse_def karatsuba_aux_def 
	          karatsuba_nat_def 
	(* Short (but slower) Proof
  apply (rewrite at "Let (limb_sz^_) _" Let_def)
	apply (refine_rcg)
  apply (refine_dref_type)
  using assms
  apply clarsimp
  apply (simp_all add: big_int_rel_def in_br_conv)
  by (clarsimp; presburger add: karatsuba_refine_aux)
  *)
  
  (* Step by Step Proof *)
	apply (rule refine)
	apply refine_mono
	apply (refine_dref_type) []
	subgoal using assms by auto

	apply (rule prod_case_refine, assumption)
	
	apply (rule refine)

	subgoal by (metis big_int_length_zero_rel')
	subgoal by (simp add: big_int_rel_def in_br_conv)
	
	apply (rule refine)
	subgoal by (metis big_int_length_zero_rel')
	subgoal by (simp add: big_int_rel_def in_br_conv)
	
	apply (rule refine)
  subgoal using big_int_rel_bounds
    by (metis big_int_rel_size_leq le_antisym nat_geq_1_eq_neqz power_one_right)

  subgoal by (refine_vcg big_int_mult_small_correct)


	apply (rule refine)
  subgoal using big_int_rel_bounds
    by (metis big_int_rel_size_leq le_antisym nat_geq_1_eq_neqz power_one_right)

  subgoal by (refine_vcg big_int_mult_small_correct)

  apply (rule refine)
  subgoal by presburger

  apply (rule refine)
  subgoal by presburger

	apply (rule Let_unfold_refine)

	apply (rule Let_unfold_refine)
	apply (rule Let_unfold_refine)

	apply (rule remove_Let_refine)


	apply (rule bind_Let_refine2)
	apply (rule big_int_take_correct_eq)
  subgoal using big_int_rel_length_log by presburger
	apply assumption

	apply (rule bind_Let_refine2)
	apply (rule big_int_drop_correct_eq)
  subgoal using big_int_rel_length_log by presburger
	apply assumption

	apply (rule bind_Let_refine2)
	apply (rule big_int_take_correct_eq)
  subgoal using big_int_rel_length_log by presburger
  apply assumption

	apply (rule bind_Let_refine2)
	apply (rule big_int_drop_correct_eq)
  subgoal using big_int_rel_length_log by presburger
	apply assumption


  apply (rewrite while.imonad2)
	apply (rule bind_Let_refine2)

	apply (rule big_int_add_correct)
  apply assumption+

	apply (rule bind_Let_refine2)
	apply (rule big_int_add_correct)
	apply assumption+

	apply (rule refine)
	apply (refine_dref_type) []
	subgoal by (meson prod_rel_simp)

	apply (rule refine)

	apply (refine_dref_type) []
	subgoal by (meson prod_rel_simp)

	apply (rule bind_Let_refine2)
	apply (rule big_int_add_correct)
	apply assumption+


	apply (rule refine)
	apply (refine_dref_type) []
	subgoal by (meson prod_rel_simp)

	apply (rule refine)

	apply (rule bind_Let_refine2)
	apply (rule big_int_sub_compl_correct)
	apply assumption+

	apply (rule bind_Let_refine2)
	apply (rule big_int_rshift_correct_eq)
  subgoal using big_int_rel_length_log by presburger
		
	apply assumption

	apply (rule bind_Let_refine2)
	apply (rule big_int_add_correct)
	apply assumption+

	apply (rule bind_Let_refine2)
	 apply (rule big_int_rshift_correct_sqr_eq)

  subgoal using big_int_rel_length_log by metis
  apply assumption

  apply (rewrite while.imonad2)

	apply (rule big_int_add_correct)
	apply assumption
	apply assumption
	done

lemma karatsuba_correct[refine]:
	assumes "(ai,a)\<in>big_int_rel" "(bi,b)\<in>big_int_rel" 
	shows "karatsuba ai bi \<le> \<Down>big_int_rel (RETURN (a*b))"
proof -
	note karatsuba_refine 
	also note karatsuba_nat_correct' 
	finally show ?thesis using assms .
qed  

lemma karatsuba_correct'[refine]:
	assumes "(ai,a)\<in>big_int_rel" "(bi,b)\<in>big_int_rel" 
	shows "karatsuba ai bi \<le> SPEC (\<lambda> ci. (ci, (a*b)) \<in> big_int_rel)"
	using karatsuba_correct
	by (simp add: assms(1,2) conc_fun_RETURN)

thm_oracles karatsuba_correct
thm_deps karatsuba_correct

end
