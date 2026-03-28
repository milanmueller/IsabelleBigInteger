theory BigInteger
  imports BaseDecomp WordOps
begin

(* TODO: replace BigInt.thy with this theory once finished *)

lemma limb_sz_base[simp]: "base_decomp limb_sz"
  unfolding limb_sz_unfold base_decomp_def by simp

(* Question: Local lemmas for limb_sz *)

global_interpretation limb_base: base_decomp limb_sz
  defines nat_to_nat_list = "base_decomp.base_decomp limb_sz"
  and limb_digits = "base_decomp.digits limb_sz"
  and nat_list_to_nat = "base_decomp.base_\<alpha> limb_sz"
  and nat_list_invar = "base_decomp.base_invar limb_sz"
  and limb_base_rel = "base_decomp.base_rel limb_sz"
  and limb_base_strict_rel = "base_decomp.base_strict_rel limb_sz"
  by (unfold_locales; simp add: limb_sz_unfold)


section \<open>Unsigned Big Integer Type\<close>

type_synonym BI = "limb list"

definition BI_len :: "BI \<Rightarrow> nat" where
  "BI_len ai \<equiv> length ai"

(* 
  Dynamic check if index is in range
  Returns limb at an index or 0 if outside
*)
definition BI_get_or_zero :: "BI \<Rightarrow> nat \<Rightarrow> limb" where
  "BI_get_or_zero ai i \<equiv> if i < BI_len ai then ai ! i else 0"

(* 
  Precondition: i is in range 
  Returns limb at index
*)
definition BI_get :: "BI \<Rightarrow> nat \<Rightarrow> limb nres" where 
  "BI_get ai i \<equiv> doN {
    ASSERT (i < BI_len ai);
    RETURN (ai ! i)
  }"

definition BI_get_last :: "BI \<Rightarrow> limb" where
  "BI_get_last ai \<equiv> op_list_last ai"

definition BI_append :: "BI \<Rightarrow> limb \<Rightarrow> BI nres" where
  "BI_append ai x \<equiv> doN {
    \<comment> \<open>TODO: Include assumptions about index size < 2 ^ 64 once done\<close>
    RETURN (ai @ [x])
  }"

definition BI_pop :: "BI \<Rightarrow> BI nres" where
  "BI_pop ai \<equiv> mop_list_butlast ai"

definition BI_\<alpha> :: "BI \<Rightarrow> nat" where
  "BI_\<alpha> xs = horner_sum limb_nat limb_sz xs"

(* This ensures no trailing 0 digits *)
definition BI_invar :: "BI \<Rightarrow> bool" where
  "BI_invar xs \<equiv> (xs = [] \<or> last xs \<noteq> 0)"

definition BI_rel :: "(BI \<times> nat) set" where
  "BI_rel \<equiv> br BI_\<alpha> BI_invar"

(* This restores the invariant *)
definition BI_trim :: "BI \<Rightarrow> BI nres" where 
  "BI_trim ai \<equiv> doN {
    bi \<leftarrow> WHILEIT
      (\<lambda>bi. BI_\<alpha> bi = BI_\<alpha> ai)
      (\<lambda>bi. BI_len bi > 0 \<and> BI_get_last bi = 0)
      mop_list_butlast
      ai;
    RETURN bi
  }"

lemma nat_list_abs: "nat_list_to_nat (map (limb_nat) xs) = BI_\<alpha> xs"
  unfolding BI_\<alpha>_def
  using limb_base.base_decomp_inv_horner_sum horner_sum_id_map
  by auto

lemma limb_nat_base_invar: "nat_list_invar (map limb_nat ai)"
proof -
  have 1:"nat_list_invar (map limb_nat ai)
    = (\<lambda>xs. \<forall>x. x \<in> set xs \<longrightarrow> x < limb_sz) (map limb_nat ai)"
    using limb_base.base_invar_def by presburger
  have 2:"... = (\<forall>x. x \<in> set (map limb_nat ai) \<longrightarrow> x < limb_sz)"
    by simp
  have 3:"... = True" using limb_nat_lt 
    by force 
  thus "nat_list_invar (map limb_nat ai)" using 1 2 by satx
qed


lemma BI_rel_base_rel: "(ai, a) \<in> BI_rel \<Longrightarrow> (map limb_nat ai, a) \<in> limb_base_rel"
proof -
  assume "(ai, a) \<in> BI_rel"
  hence "BI_\<alpha> ai = a" unfolding BI_rel_def in_br_conv by simp
  hence base_\<alpha>: "nat_list_to_nat (map limb_nat ai) = a" using nat_list_abs by blast

  have base_invar: "nat_list_invar (map limb_nat ai)" 
    using limb_nat_base_invar by simp

  show ?thesis
    by (metis in_br_conv base_\<alpha> base_invar limb_base.base_rel_def)
qed

lemma BI_rel_base_strict_rel: "(ai, a) \<in> BI_rel \<Longrightarrow> (map limb_nat ai, a) \<in> limb_base_strict_rel"
  unfolding limb_base_strict_rel_def base_decomp.base_strict_rel_alt[OF limb_sz_base] BI_rel_def in_br_conv
    nat_list_abs[symmetric] BI_invar_def limb_base.base_strict_invar_def
  apply auto
  oops

section \<open>Unsigned Big Integer Constants\<close>

definition BI_ZERO :: "BI" where "BI_ZERO \<equiv> []"

lemma BI_ZERO_correct[simp]: "BI_invar BI_ZERO" "BI_\<alpha> BI_ZERO = 0"
  unfolding BI_ZERO_def BI_\<alpha>_def BI_invar_def 
  by simp+

lemma BI_ZERO_refine[simp]: "(BI_ZERO, 0) \<in> BI_rel"
  unfolding BI_rel_def in_br_conv 
  by simp

definition BI_ONE :: "BI" where "BI_ONE \<equiv> [1]"

lemma BI_ONE_correct[simp]: "BI_invar BI_ONE" "BI_\<alpha> BI_ONE = 1"
  unfolding BI_ONE_def BI_\<alpha>_def BI_invar_def 
  by simp+

lemma BI_ONE_refine[simp]: 
  "(BI_ONE, 1) \<in> BI_rel"
  "(BI_ONE, Suc 0) \<in> BI_rel"
  unfolding BI_rel_def in_br_conv
  by simp+

definition BI_TWO :: "BI" where "BI_TWO \<equiv> [2]"

lemma BI_TWO_correct[simp]: "BI_invar BI_TWO" "BI_\<alpha> BI_TWO = 2"
  unfolding BI_TWO_def BI_\<alpha>_def BI_invar_def 
  apply simp+
  using limb_base.base_decomp.simps(1) limb_nat_def by fastforce

lemma BI_TWO_refine[simp]: 
  "(BI_TWO, 2) \<in> BI_rel"
  unfolding BI_rel_def in_br_conv
  by simp+

definition BI_LIMB_MAX :: "BI" where "BI_LIMB_MAX \<equiv> [-1]"

lemma BI_LIMB_MAX_correct[simp]: "BI_invar BI_LIMB_MAX" "BI_\<alpha> BI_LIMB_MAX = limb_mx"
  unfolding BI_LIMB_MAX_def BI_\<alpha>_def BI_invar_def 
  apply simp+
  unfolding limb_mx_unfold
  by (metis limb_nat_def unat_minus_one_word)

lemma BI_LIMB_MAX_refine[simp]: 
  "(BI_LIMB_MAX, limb_mx) \<in> BI_rel"
  unfolding BI_rel_def in_br_conv
  by simp+

definition BI_LIMB_SIZE :: "BI" where "BI_LIMB_SIZE \<equiv> [0, 1]"

lemma BI_LIMB_SIZE_correct[simp]: "BI_invar BI_LIMB_SIZE" "BI_\<alpha> BI_LIMB_SIZE = limb_sz"
  unfolding BI_LIMB_SIZE_def BI_\<alpha>_def BI_invar_def 
  by simp+

lemma BI_LIMB_SIZE_refine[simp]: 
  "(BI_LIMB_SIZE, limb_sz) \<in> BI_rel"
  unfolding BI_rel_def in_br_conv
  by simp+

section \<open>Base Abstraction Properties Lifted to Big Integers\<close>

lemma BI_drop: "BI_\<alpha> (drop i ai) = (BI_\<alpha> ai) div limb_sz ^ i" 
  unfolding nat_list_abs[symmetric] drop_map[symmetric]
  using limb_nat_base_invar limb_base.base_drop 
  by blast

lemma BI_append: "BI_\<alpha> (ls1 @ ls2) = BI_\<alpha> ls1 + (BI_\<alpha> ls2) * (limb_sz ^ length ls1)"
  unfolding nat_list_abs[symmetric] map_append
  using limb_nat_base_invar limb_base.base_append
  by simp
 
lemma BI_take: "BI_\<alpha> (take i ai) = (BI_\<alpha> ai) mod (limb_sz ^ i)"
  unfolding nat_list_abs[symmetric] take_map[symmetric]
  using limb_nat_base_invar limb_base.base_take
  by simp

lemma BI_snoc: "BI_\<alpha> (ls1 @ [x]) = BI_\<alpha> ls1 + limb_nat x * limb_sz ^ length ls1"
  unfolding BI_append 
  using BI_\<alpha>_def 
  by simp

lemma BI_take_Suc: "BI_\<alpha> (take (Suc n) list) 
  = BI_\<alpha> (take n list) + limb_nat (BI_get_or_zero list n) * limb_sz ^ n"
  unfolding BI_get_or_zero_def BI_len_def 
  apply (cases "Suc n \<le> length list")
  subgoal proof -
    assume n_lt: "Suc n \<le> length list"
    hence "BI_\<alpha> (take (Suc n) list) = BI_\<alpha> ((take n list) @ [list ! n])"
      by (simp add: take_Suc_conv_app_nth)
    also have "... = BI_\<alpha> (take n list) + limb_nat (list ! n) * limb_sz ^ n"
      using BI_snoc n_lt by simp
    finally show ?thesis using n_lt by auto
  qed
  by simp

lemma BI_butlast: 
   "list \<noteq> [] \<Longrightarrow> BI_\<alpha> list = BI_\<alpha> (butlast list) 
     + limb_nat (BI_get_last list) * limb_sz ^ (BI_len list - 1)"
proof -
  assume list: "list \<noteq> []" hence len: "length list \<ge> 1" by simp
  hence "take (Suc (length list - 1)) list = list" using take_all by simp 
  hence "BI_\<alpha> list = BI_\<alpha> (take (length list - 1) list) 
      + limb_nat (BI_get_or_zero list (length list - 1)) * limb_sz ^ (length list - 1)"
    using BI_take_Suc by metis
  also have "... = BI_\<alpha> (butlast list) 
      + limb_nat (BI_get_or_zero list (length list - 1)) * limb_sz ^ (length list - 1)"
    using butlast_conv_take by simp   
  finally show ?thesis
    unfolding BI_get_last_def BI_get_or_zero_def BI_len_def op_list_last_def last_conv_nth[OF list]
    using len by simp
qed

lemma limb_nat_zero: "x \<noteq> 0 \<longleftrightarrow> limb_nat x \<noteq> 0" 
  unfolding limb_nat_def
  by (metis unat_eq_zero)

corollary last_limb_zero: "ai \<noteq> [] \<Longrightarrow> last ai \<noteq> 0 \<longleftrightarrow> last (map limb_nat ai) \<noteq> 0"
  unfolding last_map limb_nat_zero by simp

lemma BI_rel_unique: 
  "(ai, a) \<in> BI_rel \<Longrightarrow> (bi, b) \<in> BI_rel \<Longrightarrow> (a = b) \<longleftrightarrow> (ai = bi)"
  unfolding BI_rel_def in_br_conv nat_list_abs[symmetric] BI_invar_def 
  using limb_base.base_decomp_bij 
  apply auto
  subgoal
    apply (cases "bi \<noteq> []")
    apply (auto simp: limb_base.base_decomp_inv_not_zero)
    by (meson limb_base.base_decomp_inv_not_zero last_limb_zero list.map_disc_iff)
  subgoal
    apply (cases "ai \<noteq> []")
    apply (auto simp: limb_base.base_decomp_inv_not_zero)
    by (meson last_limb_zero list.map_disc_iff limb_base.base_decomp_inv_not_zero)
  subgoal 
    apply (cases "ai \<noteq> []")
    apply (cases "bi \<noteq> []")
    apply simp_all
    oops

lemma BI_rel_bij: "(ai, a) \<in> BI_rel \<Longrightarrow> nat_to_nat_list a = map limb_nat ai"
  unfolding BI_rel_def in_br_conv nat_list_abs[symmetric] BI_invar_def
  oops



  


end