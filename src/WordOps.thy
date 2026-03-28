theory WordOps
  imports Setup
begin       

subsection \<open>Word Limb Definition\<close>

type_synonym limb\<^sub>w = 64
type_synonym limb = "limb\<^sub>w word"
definition limb_wd :: nat where "limb_wd \<equiv> LENGTH(limb\<^sub>w)" (* limb width - nr of bits *)
definition limb_sz :: nat where "limb_sz \<equiv> 2 ^ limb_wd" (* limb size - nr of possible values *)
definition limb_mx :: nat where "limb_mx \<equiv> 2 ^ limb_wd - 1" (* limb max - max value as nat *)

type_synonym double\<^sub>w = 128
type_synonym double_limb = "double\<^sub>w word"
definition double_wd :: nat where "double_wd \<equiv> LENGTH(double\<^sub>w)" (* double limb width *)

lemma limb_mx_suc: 
  "Suc limb_mx = limb_sz"
  "limb_sz = limb_mx + 1"
  unfolding limb_mx_def limb_sz_def limb_wd_def 
  by simp_all

lemma limb_sz_unfold: 
  "limb_sz = 2 ^ LENGTH(limb\<^sub>w)"
  unfolding limb_sz_def limb_wd_def 
  by blast

lemma limb_mx_unfold:
  "limb_mx = 2 ^ LENGTH(limb\<^sub>w) - 1"
  unfolding limb_mx_def limb_wd_def 
  by blast

lemma limb_sz_gt[simp]: "limb_sz > 1" "limb_sz > 4" 
  unfolding limb_sz_unfold 
  by simp_all

definition limb_nat :: "limb \<Rightarrow> nat" where "limb_nat = unat"
definition nat_limb :: "nat \<Rightarrow> limb" where "nat_limb = word_of_nat"

lemma limb0[simp]: 
  "nat_limb 0 = 0" 
  "limb_nat 0 = 0"
  unfolding nat_limb_def limb_nat_def
  by simp_all

lemma limb1[simp]: 
  "nat_limb 1 = 1" 
  "nat_limb (Suc 0) = 1" 
  "limb_nat 1 = 1"
  unfolding nat_limb_def limb_nat_def
  by simp_all

lemma limb_nat_id: 
  "nat_limb \<circ> limb_nat = id"
  "nat_limb (limb_nat x) = x"
  unfolding nat_limb_def limb_nat_def
  by simp_all

lemma nat_limb_mod:
  "limb_nat (nat_limb x) = x mod limb_sz"
  unfolding nat_limb_def limb_nat_def limb_sz_unfold
  using unat_of_nat 
  by blast

lemma limb_nat_le: 
  "limb_nat x \<le> limb_mx"
proof -
  have "limb_nat x < limb_sz"
    unfolding limb_nat_def limb_sz_unfold 
    using unat_lt2p by blast
  hence "limb_nat x \<le> limb_sz - 1"
    by linarith
  thus ?thesis using limb_mx_suc 
    by auto
qed

lemma limb_nat_lt[simp]:
  "limb_nat x < limb_sz"
  unfolding limb_mx_suc(2) 
  using limb_nat_le less_eq_iff_succ_less 
  by blast

subsection \<open>Limb Addition with Carry\<close>

lemma limb_add: "a + b = nat_limb (limb_nat a + limb_nat b)"
  unfolding nat_limb_def limb_nat_def
  by force

lemma limb_compare: "a \<le> b \<longleftrightarrow> limb_nat a \<le> limb_nat b"
  unfolding limb_nat_def using word_le_nat_alt 
  by blast

definition add_carry :: "limb \<Rightarrow> limb \<Rightarrow> limb \<Rightarrow> (limb \<times> limb)"
  where "add_carry a b c \<equiv> (let sum = a + b + c in (sum, 
      if (c = 0)
        then (if sum < a then 1 else 0)
        else (if sum \<le> a then 1 else 0)))"

lemma add_carry_bit: "snd (add_carry a b c) \<in> {0, 1}"
  unfolding add_carry_def Let_def
  by auto

lemma nat_compare_div: "(b::nat) > 0 \<Longrightarrow> a \<ge> b \<longleftrightarrow> a div b \<ge> 1"
  using div_greater_zero_iff nat_geq_1_eq_neqz by force

(* Lemmas when carry = 0 *)
lemma add_div_cases: "(limb_nat a + limb_nat b) div limb_sz \<in> {0, 1}"
proof -
  have "limb_nat a + limb_nat b < 2 * limb_sz" 
    using limb_nat_lt[of a] limb_nat_lt[of b] by linarith
  hence "(limb_nat a + limb_nat b) div limb_sz < 2"
    using less_mult_imp_div_less by blast
  thus ?thesis by (simp add: less_2_cases)
qed

lemma add_carry0_overflow: 
  "(a + b < a) \<longleftrightarrow> (limb_nat a + limb_nat b) \<ge> limb_sz"
  unfolding limb_sz_unfold limb_nat_def
  by (metis linorder_not_le no_olen_add_nat)

lemma add_carry0_overflow_bit: 
  "(a + b < a) \<longleftrightarrow> ((limb_nat a + limb_nat b) div limb_sz) = 1"
proof - 
  have 1: "(a + b < a) \<longleftrightarrow> (limb_nat a + limb_nat b) div limb_sz \<ge> 1"
    using add_carry0_overflow nat_compare_div limb_sz_gt
    by (metis limb0(2) limb_nat_lt)
  thus ?thesis using 1 add_div_cases[of a b] by auto
qed

(* Lemmas when carry = 1 *)
lemma add_inc_div_cases:
  "(limb_nat a + limb_nat b + 1) div limb_sz \<in> {0, 1}"
proof -
  have "limb_nat a + limb_nat b + 1 \<le> 2 * limb_mx + 1"
    using limb_nat_le[of a] limb_nat_le[of b]
    by linarith
  hence "limb_nat a + limb_nat b + 1 < 2 * limb_sz"
    using limb_mx_suc by auto
  hence "(limb_nat a + limb_nat b + 1) div limb_sz < 2"
    using less_mult_imp_div_less by blast
  thus ?thesis by (simp add: less_2_cases)
qed


lemma add_carry1_overflow_aux1:
  "a + b + 1 \<le> a \<Longrightarrow> limb_nat a + limb_nat b + 1 \<ge> limb_sz"
proof -
  have 1: "limb_nat (a + b + 1) = (limb_nat a + limb_nat b + 1) mod limb_sz"
    using limb1 limb_add nat_limb_mod by presburger
  
  assume "a + b + 1 \<le> a"
  hence "limb_nat (a + b + 1) \<le> limb_nat a"
    using limb_compare by auto
  hence "(limb_nat a + limb_nat b + 1) mod limb_sz \<le> limb_nat a"
    unfolding 1 by auto
  thus ?thesis 
    using zero_neq_one by fastforce
qed

lemma add_carry1_overflow:
  "a + b + 1 \<le> a  \<longleftrightarrow> limb_nat a + limb_nat b + 1 \<ge> limb_sz"
  apply (rule iffI)
  subgoal using add_carry1_overflow_aux1[of a b] by simp
  subgoal proof -
    have cmp: "a + b + 1 \<le> a \<longleftrightarrow> limb_nat (a + b + 1) \<le> limb_nat a"
      using limb_compare by auto
    
    have mod: "limb_nat (a + b + 1) = (limb_nat a + limb_nat b + 1) mod limb_sz"
      using limb1 limb_add nat_limb_mod by presburger

    have "limb_nat a + limb_nat b + 1 \<le> 2 * limb_mx + 1"
      using limb_nat_le[of a] limb_nat_le[of b]
      by linarith
    hence sum: "limb_nat a + limb_nat b + 1 < 2 * limb_sz"
      using limb_mx_suc by auto

    assume "limb_nat a + limb_nat b + 1 \<ge> limb_sz"
    hence div: "(limb_nat a + limb_nat b + 1) div limb_sz = 1"
      using sum nat_div_eq_Suc_0_iff by presburger

    have sum: "limb_nat a + limb_nat b + 1 = 
            (limb_nat a + limb_nat b + 1) mod limb_sz +
            limb_sz * ((limb_nat a + limb_nat b + 1) div limb_sz)"
      using mod_mult_div_eq[of "limb_nat a + limb_nat b + 1" limb_sz]
      by presburger

    hence "limb_nat a + limb_nat b + 1 = limb_nat (a + b + 1) + limb_sz"
      using div mod
      by (metis nat_mult_1_right)
    thus ?thesis using add_carry0_overflow cmp inc_le by fastforce
  qed
  done

lemma add_carry1_overflow_bit:
  "a + b + 1 \<le> a  \<longleftrightarrow> (limb_nat a + limb_nat b + 1) div limb_sz = 1"
proof -
  have gt: "a + b + 1 \<le> a  \<longleftrightarrow> limb_nat a + limb_nat b + 1 \<ge> limb_sz" 
    using add_carry1_overflow by simp

  have "limb_nat a + limb_nat b + 1 \<le> 2 * limb_mx + 1"
    using limb_nat_le[of a] limb_nat_le[of b]
    by linarith
  hence "limb_nat a + limb_nat b + 1 < 2 * limb_sz"
    using limb_mx_suc by auto
  thus ?thesis
    using gt nat_div_eq_Suc_0_iff by presburger
qed

lemma add_carry_correct:
  assumes "c \<in> {0, 1}" and "s = (limb_nat a + limb_nat b + limb_nat c)"
  shows "limb_nat ( fst ( add_carry a b c )) = s mod limb_sz" 
  and "limb_nat ( snd ( add_carry a b c )) = s div limb_sz"
  unfolding add_carry_def Let_def assms(2)
  subgoal by (simp add: limb_nat_def limb_sz_unfold mod_add_left_eq unat_word_ariths(1))
  subgoal 
    using assms add_carry1_overflow_bit add_inc_div_cases
                add_carry0_overflow_bit add_div_cases
    by fastforce
  done

lemma add_carry_unfold:
  "c \<in> {0, 1} \<Longrightarrow> add_carry a b c = (x, y) 
  \<Longrightarrow> limb_nat x = (limb_nat a + limb_nat b + limb_nat c) mod limb_sz
  \<and>   limb_nat y = (limb_nat a + limb_nat b + limb_nat c) div limb_sz"
  using add_carry_correct fst_conv snd_conv by metis
  
  
lemma add_carry_sum:
  assumes "c \<in> {0, 1}"
  shows "limb_nat a + limb_nat b + limb_nat c = 
    limb_sz * limb_nat ( snd ( add_carry a b c ))
    + limb_nat ( fst ( add_carry a b c ))"
  using assms add_carry_correct
  by simp

subsection \<open>Limb Multiplication with Carry\<close>

abbreviation extend :: "limb \<Rightarrow> double_limb" where "extend \<equiv> UCAST(limb\<^sub>w \<rightarrow> double\<^sub>w)"
abbreviation cutoff :: "double_limb \<Rightarrow> limb" where "cutoff \<equiv> UCAST(double\<^sub>w \<rightarrow> limb\<^sub>w)"


lemma limb_mul: "a * b = nat_limb (limb_nat a * limb_nat b)"
  unfolding nat_limb_def limb_nat_def
  by force

lemma cutoff_limb: "cutoff x = nat_limb (unat x)"
  unfolding nat_limb_def
  by force

lemma cutoff_shift_limb: "cutoff (shiftr x limb_wd) = nat_limb (unat x div limb_sz)"
  unfolding nat_limb_def cutoff_limb limb_sz_def shiftr_div_2n'
  by blast

lemma extend_fits: 
  assumes "x < limb_sz\<^sup>2"
  shows "limb_nat (cutoff (word_of_nat x)) = x mod limb_sz" and
        "limb_nat (cutoff (shiftr (word_of_nat x) limb_wd)) = x div limb_sz"
  using assms 
  unfolding limb_nat_def limb_sz_unfold 
  unfolding unat_ucast unat_of_nat
  subgoal by force
  subgoal 
    unfolding shiftr_div_2n' limb_wd_def
    using assms
    by (simp add: limb_sz_unfold unat_of_nat_len)
  done

definition mul_add :: "limb \<Rightarrow> limb \<Rightarrow> limb \<Rightarrow> (limb \<times> limb)"
  where "mul_add a b c \<equiv> (let res = (extend a * extend b + extend c) in 
    (cutoff res, cutoff (shiftr res limb_wd)))"

lemma mul_add_fits: 
  "limb_nat a * limb_nat b + limb_nat c < limb_sz\<^sup>2"
  "unat (extend a * extend b + extend c) = limb_nat a * limb_nat b + limb_nat c"
  subgoal proof -
    have a_lt: "limb_nat a \<le> limb_mx" using limb_nat_le by auto
		have b_lt: "limb_nat b \<le> limb_mx" using limb_nat_le by auto
		have c_lt: "limb_nat c \<le> limb_mx" using limb_nat_le by auto

    have aux: "limb_sz * limb_sz = limb_mx * limb_mx + 2 * limb_mx + 1"
    unfolding limb_mx_suc by simp

    have "limb_nat a * limb_nat b + limb_nat c \<le> limb_mx * limb_mx + limb_mx"
      using a_lt b_lt c_lt by (simp add: add_le_mono mult_le_mono)    
    hence res_fits: "limb_nat a * limb_nat b + limb_nat c < limb_sz * limb_sz"
      using aux by simp
    thus ?thesis by (simp add: power2_eq_square)
  qed
  subgoal proof -
		define res where "res = extend a * extend b + extend c"
		have res_eq: "res = word_of_nat (limb_nat a * limb_nat b + limb_nat c)"
			using res_def limb_nat_def by simp

		note \<open>limb_nat a * limb_nat b + limb_nat c < limb_sz\<^sup>2\<close>
    hence "limb_nat a * limb_nat b + limb_nat c < 2 ^ double_wd"
      unfolding limb_sz_unfold double_wd_def
      by auto
    thus ?thesis
      unfolding double_wd_def
      by (metis res_def res_eq unat_of_nat_len)
	qed
	done

lemma mul_add_correct: 
  "limb_nat (fst (mul_add a b c)) = (limb_nat a * limb_nat b + limb_nat c) mod limb_sz"
  "limb_nat (snd (mul_add a b c)) = (limb_nat a * limb_nat b + limb_nat c) div limb_sz"
  unfolding mul_add_def Let_def
  subgoal using mul_add_fits extend_fits by (simp add: cutoff_limb nat_limb_mod)
  subgoal using extend_fits limb_nat_def mul_add_fits by force
  done

lemma mul_add_sum: 
  "limb_nat a * limb_nat b + limb_nat c = 
    limb_sz * limb_nat (snd (mul_add a b c))
    + limb_nat (fst (mul_add a b c))"
  using mul_add_correct by presburger

subsection \<open>Limb Complement\<close>

definition compl :: "limb \<Rightarrow> limb"
  where "compl x = NOT x"

lemma compl_correct: 
  "limb_nat (x + compl x) = limb_mx"
  "limb_nat x + limb_nat (compl x) = limb_mx"
  unfolding compl_def limb_mx_unfold limb_nat_def
  subgoal by (simp add: unat_minus_one_word)
  subgoal
    by (metis unat_minus_one_word unat_plus_simple word_add_not word_order.extremum)
  done

lemma compl_sub:
  "a - b = a + compl b + 1"
proof -
  have 1: "limb_nat b + limb_nat (compl b) + 1 = limb_sz"
    using compl_correct limb_mx_suc by auto
  hence "b + compl b + 1 = 0"
    by (metis add.commute add_le_same_cancel2 compl_correct(1) less_eq_iff_succ_less limb_nat_def limb_nat_le not_add_less1
        word_overflow_unat)
  hence "a + b + compl b + 1 = a"
    by (simp add: ab_semigroup_add_class.add_ac(1))
  then show ?thesis
    using add_eq_0_iff by force
qed

(* TODO: check if this is faster then 1s complement *)
definition sub_carry :: "limb \<Rightarrow> limb \<Rightarrow> limb \<Rightarrow> (limb \<times> limb)"
  where "sub_carry a b c \<equiv> (let res = a - b - c in
    (res, if (c = 0)
      then if res > a then 1 else 0
      else if res \<ge> a then 1 else 0))"

lemma sub_carry_under:
  assumes "c \<in> {0, 1}" and "(f, s) = sub_carry a b c" and "limb_nat a \<ge> limb_nat b + limb_nat c"
  shows "limb_nat f = limb_nat a - limb_nat b - limb_nat c" and "s = 0"
  using assms unfolding sub_carry_def Let_def
  apply clarsimp
  subgoal 
    by (smt (verit) add_diff_cancel_left' add_leE diff_diff_eq diff_is_0_eq limb_nat_def unat_plus_simple word_le_nat_alt
        zadd_diff_inverse)
  using assms unfolding sub_carry_def Let_def
  apply clarsimp
  subgoal 
    by (smt (verit, ccfv_threshold)
        \<open>c = 0 \<or> c = 1 \<Longrightarrow> limb_nat b + limb_nat c \<le> limb_nat a \<Longrightarrow> f = a - b - c \<Longrightarrow> s = (if c = 0 then if a < a - b - c then 1 else 0 else if a \<le> a - b - c then 1 else 0) \<Longrightarrow> limb_nat (a - b - c) = limb_nat a - (limb_nat b + limb_nat c)\<close>
        add_leD2 dual_order.trans le_add1 le_add_same_cancel1 le_def le_diff_iff' limb1(3) limb_nat_def minus_nat.diff_0
        not_one_le_zero sub_wrap_lt unat_mono word_less_eq_iff_unsigned)
  done

lemma sub_carry_over:
  assumes "c \<in> {0, 1}" and "(f, s) = sub_carry a b c" and "limb_nat a < limb_nat b + limb_nat c"
  shows "limb_nat f = limb_sz + limb_nat a - limb_nat b - limb_nat c" and "s = 1"
  using assms unfolding sub_carry_def Let_def
  apply clarsimp
  subgoal
    by (smt (verit) ab_group_add_class.ab_diff_conv_add_uminus ab_semigroup_add_class.add_ac(1) add.commute add.right_neutral
        add_diff_cancel_right add_diff_cancel_right' compl_correct(2) compl_sub diff_is_0_eq diff_zero le_m1_iff_lt less_1_simp
        limb_mx_suc(1) limb_nat_def not_less_iff_gr_or_eq order.strict_iff_not plus_1_eq_Suc sub_wrap unat_plus_simple unsigned_1
        word_le_less_eq zadd_diff_inverse)
  using assms unfolding sub_carry_def Let_def
  apply clarsimp
  subgoal
    by (smt (verit, del_insts) add_cancel_right_right add_diff_cancel_left' diff_diff_eq diff_is_0_eq limb_nat_def
        linorder_not_le nle_le olen_add_eqv unat_plus_simple word_less_1 zadd_diff_inverse)
  done

lemma sub_carry_snd_bit:
  assumes "c \<in> {0, 1}" and "(f, s) = sub_carry a b c"
  shows "s \<in> {0, 1}"
  apply (cases "limb_nat a < limb_nat b + limb_nat c")
  using sub_carry_under sub_carry_over assms
  apply fast
  using sub_carry_under sub_carry_over assms
  by (metis insert_iff le_neq_implies_less nat_le_linear)

lemma sub_carry_correct:
  assumes "c \<in> {0, 1}" and "(f, s) = sub_carry a b c"
  shows "limb_nat a + limb_sz * limb_nat s = limb_nat f + limb_nat b + limb_nat c"
  using assms
  apply (cases "limb_nat a < limb_nat b + limb_nat c")
  subgoal proof - 
    assume c: "c \<in> {0, 1}"
    assume sub: "(f, s) = sub_carry a b c"
    assume as: "limb_nat a < limb_nat b + limb_nat c"
    hence "s = 1" using sub_carry_over[of c f s a b] sub c by blast
    hence s: "limb_nat s = 1" by simp

    have "limb_sz + limb_nat a \<ge> limb_nat b + limb_nat c"
      using assms
      by (metis add_mono insert_iff le_add1 le_add_same_cancel1 limb_mx_suc(2) limb_nat_def limb_nat_le nat_arith.rule0 singletonD unsigned_0 unsigned_1)
    thus ?thesis using sub_carry_over[of c f s a b] s sub c as by simp
  qed
  subgoal proof - 
    assume c: "c \<in> {0, 1}"
    assume sub: "(f, s) = sub_carry a b c"
    assume as: " \<not> limb_nat a < limb_nat b + limb_nat c"
    hence "s = 0" using sub_carry_under[of c f s a b] sub c by simp
    hence s: "limb_nat s = 0" by simp

    thus ?thesis using sub_carry_under[of c f s a b] s sub c as by simp
  qed
  done




find_unused_assms
unused_thms

end