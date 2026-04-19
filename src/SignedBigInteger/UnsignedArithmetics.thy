theory UnsignedArithmetics
  imports Basic LLVM_CodeGen_Auxiliary
begin

text \<open>This Theory reimplments operations from "../BigInt.thy" but for the @{typ signed_big_int} interpreting
  them as unsigned numbers. This is required because directly using the operations on @{typ big_int} would
  require us to unpack the tuple of @{typ signed_big_int} which in turn means we would have to destroy the arguments.\<close>

section "Translation"
definition "signed_big_int_abs_\<alpha> ai \<equiv> big_int_\<alpha> $ limbs_of ai"
lemma signed_bit_int_abs_\<alpha>_correct: "int $ signed_big_int_abs_\<alpha> ai = abs $ signed_big_int_\<alpha> ai"
  unfolding signed_big_int_abs_\<alpha>_def signed_big_int_to_int_def by fastforce

section "Addition"

definition signed_big_int_add_cond :: "signed_big_int \<Rightarrow> signed_big_int \<Rightarrow> (big_int \<times> nat \<times> limb) \<Rightarrow> bool"
where "signed_big_int_add_cond ai bi = (
	\<lambda>(ci, idx, cr). idx < max (length_fst ai) (length_fst bi) \<or> (cr > 0)
)"
lemma signed_big_int_add_cond_correct:
  "signed_big_int_add_cond ai bi = big_int_add_cond (limbs_of ai) (limbs_of bi)"
  by (simp add: limbs_of_def big_int_add_cond_def length_fst_def signed_big_int_add_cond_def)

definition signed_big_int_add_loop_invar :: "signed_big_int \<Rightarrow> signed_big_int \<Rightarrow> limb \<Rightarrow> (big_int \<times> nat \<times> limb) \<Rightarrow> bool"
where "signed_big_int_add_loop_invar ai bi init_cr = (
	\<lambda>(ci, idx, cr). 
  cr \<in> {0, 1}
  \<and> idx = length ci
	\<and> idx < max (length_fst ai) (length_fst bi) + 2
	\<and> big_int_to_nat (take idx (fst ai)) + big_int_to_nat (take idx (fst bi)) + limb_nat init_cr = big_int_to_nat ci + limb_nat cr * limb_sz ^ idx
)"
lemma signed_big_int_add_loop_invar_correct:
  "signed_big_int_add_loop_invar ai bi init_cr \<equiv> big_int_add_loop_invar (limbs_of ai) (limbs_of bi) init_cr"
  by (simp add: limbs_of_def big_int_add_loop_invar_def length_fst_def signed_big_int_add_loop_invar_def) 

definition signed_big_int_add_loop :: "signed_big_int \<Rightarrow> signed_big_int \<Rightarrow> limb \<Rightarrow> big_int nres" where
  "signed_big_int_add_loop ai bi init_cr \<equiv> do {
      (ci, _, _) \<leftarrow> WHILEIT 
        (signed_big_int_add_loop_invar ai bi init_cr)
        (signed_big_int_add_cond ai bi)
			(\<lambda> (ci, idx, cr) . do {
				let ai = get_or_zero_fst ai idx;
				let bi = get_or_zero_fst bi idx;
				let (r, cr) = add_carry ai bi cr;
        
        ci_next \<leftarrow> bi_append ci r;
        ASSERT (idx+1 \<le> length ci_next);
        
        let idx = idx + 1;

				RETURN (ci_next, idx, cr)
			}) (big_int0, 0, init_cr);
      RETURN ci
  }"
lemma signed_big_int_add_loop_eq_big_int_add_loop:
  "signed_big_int_add_loop ai bi init_cr = big_int_add_loop (limbs_of ai) (limbs_of bi) init_cr"
  by (simp add: limbs_of_def big_int_add_loop_def
                get_or_zero_fst_def signed_big_int_add_cond_correct
                signed_big_int_add_loop_def signed_big_int_add_loop_invar_correct)

lemma signed_big_int_add_loop_correct:
  assumes "(ai, a) \<in> signed_big_int_rel"
      and "(bi, b) \<in> signed_big_int_rel"
      and "init_cr \<in> {0,1}"
    shows "signed_big_int_add_loop ai bi init_cr \<le> SPEC (\<lambda>ci. big_int_\<alpha> ci = nat $ abs a + nat $ abs b + limb_nat init_cr)"
  unfolding signed_big_int_add_loop_eq_big_int_add_loop
  using abs_rel assms(1,2,3) big_int_add_loop_correct by presburger

definition signed_big_int_abs_add :: "signed_big_int \<Rightarrow> signed_big_int \<Rightarrow> big_int nres" where
  "signed_big_int_abs_add ai bi \<equiv> do {
	  let init_cr = 0; 
		ci \<leftarrow> signed_big_int_add_loop ai bi init_cr;
		ci \<leftarrow> big_int_trim ci;
    RETURN ci	
	}"

lemma signed_big_int_abs_add_correct:
  assumes "(ai, a) \<in> signed_big_int_rel"
      and "(bi, b) \<in> signed_big_int_rel"
    shows "signed_big_int_abs_add ai bi \<le> SPEC (\<lambda>ci. big_int_\<alpha> ci = nat $ abs a + nat $ abs b \<and> big_int_invar ci)"
  unfolding signed_big_int_abs_add_def
  apply (refine_vcg signed_big_int_add_loop_correct big_int_trim_correct)
  apply (rule assms(1))
  apply (rule assms(2))
  apply simp
  subgoal by auto
  subgoal by satx 
  done

section "Comparisons"
definition signed_big_int_abs_leq :: "signed_big_int \<Rightarrow> signed_big_int \<Rightarrow> bool nres" where
  "signed_big_int_abs_leq ai bi \<equiv> do {
    let la = length_fst ai;
    let lb = length_fst bi;
    if la = lb 
    then do {
      ASSERT (lb = la);
      if la \<ge> 1 
        then do {
          ASSERT (la \<ge> 1);
          let idx = la - 1;
          idx \<leftarrow> WHILEIT
            (\<lambda> idx . (drop (idx + 1) (fst ai) = drop (idx + 1) (fst bi)))
            \<comment> \<open>TODO: remove dynamic index check\<close> 
            (\<lambda> idx . (get_or_zero_fst ai idx = get_or_zero_fst bi idx) \<and> idx \<ge> 1)
            (\<lambda> idx . do {
              ASSERT (idx \<ge> 1);
              let idx = idx - 1;
              RETURN idx
            }) (idx);
          let aix = get_or_zero_fst ai idx;
          let bix = get_or_zero_fst bi idx;
          let res = aix \<le> bix;
          RETURN res
        }
        else RETURN True 
      }
    else RETURN (la < lb) 
  }"
lemma signed_big_int_abs_leq_eq_big_int_leq_limbs:
  "signed_big_int_abs_leq ai bi = big_int_leq (limbs_of ai) (limbs_of bi)"
  unfolding signed_big_int_abs_leq_def big_int_leq_def
            length_fst_def get_or_zero_fst_def
  using limbs_of_def big_int_length_def by presburger

lemma signed_big_int_abs_leq_correct:
  assumes "(ai, a) \<in> signed_big_int_rel" 
      and "(bi, b) \<in> signed_big_int_rel"
    shows "signed_big_int_abs_leq ai bi \<le> (\<Down> Id) (RETURN (nat $ abs a \<le> nat $ abs b))"
  unfolding signed_big_int_abs_leq_eq_big_int_leq_limbs
  using abs_rel assms(1,2) big_int_leq_correct by presburger

lemma signed_big_int_abs_leq_correct':
  assumes "(ai, a) \<in> signed_big_int_rel" 
      and "(bi, b) \<in> signed_big_int_rel"
    shows "signed_big_int_abs_leq ai bi \<le> SPEC (\<lambda>r. (r \<longleftrightarrow> nat $ abs a \<le> nat $ abs b))"
  using signed_big_int_abs_leq_correct by (simp add: assms(1,2) ireturn_eq)

text "For now we only need \<le>. TODO: Add other comparison operations (can just reuse \<le> for that)"

section "Subtraction"
text "We consider a subtraction a - b with the assumption that a \<ge> b (which is sufficient to implement proper signed addition)"

definition signed_compl_invar :: "signed_big_int \<Rightarrow> nat \<Rightarrow> big_int \<times> nat \<Rightarrow> bool" where
"signed_compl_invar ai l \<equiv> (\<lambda> (bi, idx) . 
	idx \<le> l \<and>
	length bi = idx \<and>
	big_int_\<alpha> bi + big_int_\<alpha> (take idx (fst ai)) = limb_sz ^ idx - 1
)"
lemma signed_compl_invar_correct:
  "signed_compl_invar ai l \<equiv> compl_invar (limbs_of ai) l"
  unfolding signed_compl_invar_def compl_invar_def
  using limbs_of_def by auto

definition signed_big_int_abs_compl :: "signed_big_int \<Rightarrow> nat \<Rightarrow> big_int nres" where
"signed_big_int_abs_compl ai l \<equiv> do {
	(bi, idx) \<leftarrow> WHILEIT (signed_compl_invar ai l) (compl_cond ai l) (\<lambda> (bi, idx). do {
    let aidx = (get_or_zero_fst ai idx);
    let aidx_compl = compl aidx;

    bi_next \<leftarrow> bi_append bi aidx_compl;
    ASSERT (idx+1 \<le> length bi_next);

    let idx = idx + 1;

		RETURN (bi_next, idx)
	}) (big_int0, 0);
  bi \<leftarrow> big_int_trim bi;
	RETURN bi
}"
lemma signed_big_int_abs_compl_eq_big_int_compl_limbs:
  "signed_big_int_abs_compl ai l \<equiv> big_int_compl (limbs_of ai) l"
  unfolding signed_big_int_abs_compl_def big_int_compl_def
  unfolding signed_compl_invar_correct get_or_zero_fst_def limbs_of_def compl_cond_def
  by simp

lemma signed_big_int_abs_compl_correct:
  assumes "(ai, a) \<in> signed_big_int_rel"
      and "l \<ge> length $ fst ai"
    shows "signed_big_int_abs_compl ai l \<le> SPEC (\<lambda> bi. (bi, limb_sz ^ l - (nat $ abs a) - 1) \<in> big_int_rel)"
  unfolding signed_big_int_abs_compl_eq_big_int_compl_limbs
  using abs_rel limbs_of_def assms(1,2) compl_correct' by auto

definition signed_big_int_add_inc :: "signed_big_int \<Rightarrow> signed_big_int \<Rightarrow> big_int nres"
  where "signed_big_int_add_inc ai bi \<equiv> do {
    let init_cr = 1;
		ci \<leftarrow> signed_big_int_add_loop ai bi init_cr;
    ci \<leftarrow> big_int_trim ci;
		RETURN ci
	}"

lemma signed_big_int_add_inc_correct:
  assumes "(ai, a) \<in> signed_big_int_rel"
      and "(bi, b) \<in> signed_big_int_rel"
    shows "signed_big_int_add_inc ai bi \<le> \<Down>big_int_rel (RETURN (nat $ abs a + nat $ abs b + 1))"
  by (metis abs_rel assms(1,2) big_int_add_inc_correct
            big_int_add_inc_def signed_big_int_add_inc_def
            signed_big_int_add_loop_eq_big_int_add_loop)

lemma signed_big_int_add_inc_correct':
  assumes "(ai, a) \<in> signed_big_int_rel"
      and "(bi, b) \<in> signed_big_int_rel"
    shows "signed_big_int_add_inc ai bi \<le> SPEC (\<lambda> ci. (ci, nat $ abs a + nat $ abs b + 1) \<in> big_int_rel)"
  using signed_big_int_add_inc_correct
  by (simp add: assms(1,2) conc_fun_RETURN) 

(* NOTE: this assumes abs ai \<ge> abs bi, otherwise returns limb_sz^l - nat $ abs a + nat $ abs b *)
definition "signed_big_int_sub_abs_compl ai bi \<equiv> doN {
	let l = max (length_fst ai) (length_fst bi);
	nbi \<leftarrow> signed_big_int_abs_compl bi l;
	sum \<leftarrow> signed_big_int_add_inc ai (nbi, False);
  sum \<leftarrow> big_int_take l sum;
	RETURN sum
}"            

lemma signed_big_int_sub_abs_compl_correct:
  assumes "nat $ abs a \<ge> nat $ abs b"
      and "(ai, a) \<in> signed_big_int_rel"
      and "(bi, b) \<in> signed_big_int_rel"
    shows "signed_big_int_sub_abs_compl ai bi \<le> \<Down>big_int_rel (RETURN (nat $ abs a - nat $ abs b))"
proof -
  have arel: "(limbs_of ai, nat $ abs a) \<in> big_int_rel"
    using abs_rel assms(2) by simp
  have brel: "(limbs_of bi, nat $ abs b) \<in> big_int_rel"
    using abs_rel assms(3) by simp
  have eq: "signed_big_int_sub_abs_compl ai bi = big_int_sub_compl (limbs_of ai) (limbs_of bi)"
    unfolding signed_big_int_sub_abs_compl_def big_int_sub_compl_def
              signed_big_int_abs_compl_eq_big_int_compl_limbs
              signed_big_int_add_inc_def big_int_add_inc_def
              signed_big_int_add_loop_eq_big_int_add_loop
              limbs_of_def big_int_length_def length_fst_def
    by simp
  show ?thesis
    unfolding eq
    using big_int_sub_compl_correct[OF assms(1) arel brel] .
qed

lemma signed_big_int_sub_abs_compl_correct':
  assumes "nat $ abs a \<ge> nat $ abs b"
      and "(ai, a) \<in> signed_big_int_rel"
      and "(bi, b) \<in> signed_big_int_rel"
    shows "signed_big_int_sub_abs_compl ai bi \<le> SPEC (\<lambda> ri. big_int_\<alpha> ri = nat $ abs a - nat $ abs b \<and> big_int_invar ri)"
  using signed_big_int_sub_abs_compl_correct[OF assms]
  by (simp add: SPEC_cons_rule big_int_rel_def conc_fun_RETURN in_br_conv) 

section "Multiplication"
definition "signed_big_int_mult_limb_invar ai c \<equiv> (\<lambda>(bi, idx, cr) . 
	length bi = idx \<and>
	idx \<le> length $ limbs_of ai + 1 \<and>
	(big_int_\<alpha> (take idx (limbs_of ai))) * limb_nat c = big_int_\<alpha> bi + limb_nat cr * limb_sz ^ idx
)"

definition signed_big_int_mult_limb_aux :: "signed_big_int \<Rightarrow> limb \<Rightarrow> big_int nres"
	where "signed_big_int_mult_limb_aux ai c \<equiv> do {
	(bi, idx, cr) \<leftarrow> WHILEIT 
	(signed_big_int_mult_limb_invar ai c) 
	(\<lambda> (bi, idx, cr) . idx < length_fst ai \<or> cr \<noteq> 0) 
	(\<lambda> (bi, idx, cr) . do {
			let aidx = get_or_zero_fst ai idx;
			let (rs, cr) = mul_add aidx c cr;

      bi_next \<leftarrow> bi_append bi rs;
      ASSERT (idx+1 \<le> length bi_next);

			RETURN (bi_next, idx + 1, cr)
		}
	) (big_int0, 0, 0);
	RETURN bi
	}"
lemma signed_big_int_mult_limb_aux_eq_big_int_mult_limb_aux:
  "signed_big_int_mult_limb_aux ai ci = big_int_mult_limb_aux (limbs_of ai) ci"
  unfolding signed_big_int_mult_limb_aux_def big_int_mult_limb_aux_def 
  unfolding signed_big_int_mult_limb_invar_def big_int_mult_limb_invar_def
  unfolding limbs_of_def get_or_zero_fst_def length_fst_def
  by simp

definition signed_big_int_mult_limb :: "signed_big_int \<Rightarrow> limb \<Rightarrow> big_int nres" where
  "signed_big_int_mult_limb ai c = doN {
		bi \<leftarrow> signed_big_int_mult_limb_aux ai c;
		bi \<leftarrow> big_int_trim bi;
    RETURN bi 
  }"
lemma signed_big_int_mult_limb_eq_big_int_mult_limb:
  "signed_big_int_mult_limb ai c = big_int_mult_limb (limbs_of ai) c"
  unfolding signed_big_int_mult_limb_def big_int_mult_limb_def
  unfolding signed_big_int_mult_limb_aux_eq_big_int_mult_limb_aux
  by simp

lemma signed_big_int_mult_limb_correct: 
	assumes "(ai, a) \<in> signed_big_int_rel" "c = limb_nat ci" 
	shows "signed_big_int_mult_limb ai ci \<le> \<Down> big_int_rel (RETURN (nat $ abs a * c))" 
  unfolding signed_big_int_mult_limb_def
	unfolding signed_big_int_mult_limb_aux_eq_big_int_mult_limb_aux
  unfolding big_int_mult_limb_def[symmetric]
  using abs_rel assms(1,2) big_int_mult_limb_correct by blast

definition signed_big_int_mult_school_invar :: "signed_big_int \<Rightarrow> signed_big_int \<Rightarrow> (big_int \<times> nat) \<Rightarrow> bool"
  where "signed_big_int_mult_school_invar ai bi \<equiv> (\<lambda>(ci, idx). 
    big_int_to_nat (take idx (limbs_of ai)) * big_int_to_nat (limbs_of bi) = big_int_to_nat ci \<and>
    big_int_invar ci \<and>
    idx \<le> length (limbs_of ai))"
lemma signed_big_int_mult_school_invar_eq_big_int_mult_school_invar:
  "signed_big_int_mult_school_invar ai bi = big_int_mult_school_invar (limbs_of ai) (limbs_of bi)"
  unfolding signed_big_int_mult_school_invar_def big_int_mult_school_invar_def by simp

definition signed_big_int_mult_school_cond :: "signed_big_int \<Rightarrow> signed_big_int \<Rightarrow> (big_int \<times> nat) \<Rightarrow> bool"
  where "signed_big_int_mult_school_cond ai bi \<equiv> (\<lambda>(ci, idx). idx < length_fst ai)"
lemma signed_big_int_mult_school_cond_eq_big_int_mult_school_cond:
  "signed_big_int_mult_school_cond ai bi = big_int_mult_school_cond (limbs_of ai) (limbs_of bi)"
  unfolding signed_big_int_mult_school_cond_def big_int_mult_school_cond_def limbs_of_def length_fst_def
  by simp

definition signed_big_int_mult_school_body :: "signed_big_int \<Rightarrow> signed_big_int \<Rightarrow> (big_int \<times> nat) \<Rightarrow> (big_int \<times> nat) nres"
  where "signed_big_int_mult_school_body ai bi \<equiv> (\<lambda>(ci, idx). do {
    let aidx = get_or_zero_fst ai idx;
    if aidx = 0 then 
      RETURN (ci, idx + 1)
    else do {
      aidx_bi_prod \<leftarrow> signed_big_int_mult_limb bi aidx;
      ai_bi_prod \<leftarrow> big_int_rshift idx aidx_bi_prod;
      ci \<leftarrow> big_int_add ci ai_bi_prod;
      RETURN (ci, idx + 1)
    }
})"
lemma signed_big_int_mult_school_body_eq_big_int_mult_school_body:
  "signed_big_int_mult_school_body ai bi = big_int_mult_school_body (limbs_of ai) (limbs_of bi)"
  unfolding signed_big_int_mult_school_body_def big_int_mult_school_body_def
  unfolding signed_big_int_mult_limb_eq_big_int_mult_limb
  unfolding get_or_zero_fst_def limbs_of_def
  by simp

definition signed_big_int_mult_school_aux :: "signed_big_int \<Rightarrow> signed_big_int \<Rightarrow> big_int nres"
  where "signed_big_int_mult_school_aux ai bi \<equiv> doN {
    (ci, idx) \<leftarrow> WHILEIT 
      (signed_big_int_mult_school_invar ai bi)
      (signed_big_int_mult_school_cond ai bi)
      (signed_big_int_mult_school_body ai bi)
      (big_int0, 0);
    RETURN (ci)
  }"
lemma signed_big_int_mult_school_aux_correct:
  assumes "(ai, a) \<in> signed_big_int_rel"
      and "(bi, b) \<in> signed_big_int_rel"
    shows "signed_big_int_mult_school_aux ai bi \<le> \<Down> big_int_rel (RETURN (nat $ abs a * nat $ abs b))"
proof -
  have rel_a: "(limbs_of ai, nat $ abs a) \<in> big_int_rel" using abs_rel assms(1) by blast
  have rel_b: "(limbs_of bi, nat $ abs b) \<in> big_int_rel" using abs_rel assms(2) by blast
  show ?thesis 
    unfolding signed_big_int_mult_school_aux_def
    unfolding signed_big_int_mult_school_body_eq_big_int_mult_school_body
    unfolding signed_big_int_mult_school_cond_eq_big_int_mult_school_cond
    unfolding signed_big_int_mult_school_invar_eq_big_int_mult_school_invar
    unfolding big_int_mult_school_def[symmetric]
    using big_int_mult_school_correct[OF rel_a rel_b]
    by simp
qed 

lemma big_int_mult_school_correct': 
  "(ai, a) \<in> big_int_rel \<Longrightarrow> (bi, b) \<in> big_int_rel \<Longrightarrow> big_int_mult_school ai bi \<le> SPEC (\<lambda> r. big_int_\<alpha> r = a * b \<and> big_int_invar r)"
  by (smt (verit, ccfv_threshold) SPEC_cons_rule big_int_mult_school_correct big_int_rel_def conc_fun_RETURN in_br_conv)

lemma signed_big_int_mult_school_aux_correct':
  assumes "(ai, a) \<in> signed_big_int_rel"
      and "(bi, b) \<in> signed_big_int_rel"
    shows "signed_big_int_mult_school_aux ai bi \<le> SPEC (\<lambda> r. (big_int_\<alpha> r = nat $ abs a * nat $ abs b \<and> big_int_invar r))"
proof -
  have rel_a: "(limbs_of ai, nat $ abs a) \<in> big_int_rel" using abs_rel assms(1) by blast
  have rel_b: "(limbs_of bi, nat $ abs b) \<in> big_int_rel" using abs_rel assms(2) by blast
  show ?thesis 
    unfolding signed_big_int_mult_school_aux_def
    unfolding signed_big_int_mult_school_body_eq_big_int_mult_school_body
    unfolding signed_big_int_mult_school_cond_eq_big_int_mult_school_cond
    unfolding signed_big_int_mult_school_invar_eq_big_int_mult_school_invar
    unfolding big_int_mult_school_def[symmetric]
    using big_int_mult_school_correct'[OF rel_a rel_b]
    by simp
qed

end
