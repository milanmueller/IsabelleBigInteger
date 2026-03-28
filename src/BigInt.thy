theory BigInt
  imports WordOps
begin

subsection \<open>Big Int Definition\<close>

type_synonym big_int = "limb list"

definition get_or_zero :: "big_int \<Rightarrow> nat \<Rightarrow> limb" where
  "get_or_zero ai i \<equiv> if i < length ai then ai ! i else 0"

definition get_or_zero_fast :: "big_int \<Rightarrow> nat \<Rightarrow> limb nres" where
  "get_or_zero_fast ai i \<equiv> do {
    ASSERT (i \<le> length ai);
    RETURN (ai ! i)
  }"



fun big_int_to_nat :: "big_int \<Rightarrow> nat" where
  "big_int_to_nat [] = 0"
| "big_int_to_nat (x#xs) = limb_nat x + limb_sz * (big_int_to_nat xs)"

abbreviation "big_int_\<alpha> xs \<equiv> big_int_to_nat xs"

definition big_int_invar :: "big_int \<Rightarrow> bool"
  where "big_int_invar xs \<equiv> (xs = [] \<or> last xs \<noteq> 0)"

definition "big_int_rel \<equiv> br big_int_to_nat big_int_invar"
term big_int_rel

definition big_int0 :: big_int where "big_int0 \<equiv> []"
definition big_int1 :: big_int where "big_int1 \<equiv> [1]"

lemma big_int_zero_refine[simp]:
	"(big_int0, 0) \<in> big_int_rel"
  unfolding big_int_rel_def in_br_conv big_int0_def 
  by (simp add: big_int_invar_def)

lemma big_int0_correct[simp]: "big_int_invar big_int0" "big_int_\<alpha> big_int0 = 0"
	using big_int_zero_refine
	by (simp add: big_int_rel_def in_br_conv)+

lemma big_int_one_refine[simp]: 
  "(big_int1, 1) \<in> big_int_rel"
  "(big_int1, Suc 0) \<in> big_int_rel"
  unfolding big_int_rel_def in_br_conv big_int1_def
  by (auto simp: big_int_invar_def)

lemma big_int1_correct[simp]: "big_int_invar big_int1" "big_int_\<alpha> big_int1 = 1"
	using big_int_one_refine
	by (simp add: big_int_rel_def in_br_conv)+

lemma big_int_to_nat_lt: "big_int_\<alpha> ai < limb_sz ^ (length ai)"
	apply (induction rule: big_int_to_nat.induct)
  subgoal by auto
  subgoal for x xs
    by (simp; metis limb_nat_lt add.commute mlex_bound mult.commute)
  done


function (sequential) nat_to_big_int :: "nat \<Rightarrow> big_int" where
	"nat_to_big_int 0 = []"
|	"nat_to_big_int n = nat_limb n # nat_to_big_int (n div limb_sz)"
by pat_completeness auto
termination
	supply [termination_simp] = limb_sz_unfold
	by (lexicographic_order)

abbreviation "big_int_\<gamma> n \<equiv> nat_to_big_int n"

\<comment> \<open>Assume all results fit in 2^64 addressable space\<close>
definition [simp]: "sepref_sorry_that P \<equiv> P"
lemma sepref_sorry[no_atp]: "sepref_sorry_that P" sorry

definition [simp]: "op_ASSUME_sorry_bind I m \<equiv> Refine_Basic.bind (ASSUME (sepref_sorry_that I)) (\<lambda>_. m)"
lemma pat_ASSUME_bind[def_pat_rules]:
  "Refine_Basic.bind$(ASSUME$(sepref_sorry_that$I))$(\<lambda>\<^sub>2_. m) \<equiv> UNPROTECT (op_ASSUME_sorry_bind I)$m"
  by simp

lemma id_op_ASSUME_sorry_bind[id_rules]: 
  "PR_CONST (op_ASSUME_sorry_bind I) ::\<^sub>i TYPE('a nres \<Rightarrow> 'a nres)"
  by simp

lemma arity_ASSUME_sorry_bind[sepref_monadify_arity]:
  "PR_CONST (op_ASSUME_sorry_bind I) \<equiv> \<lambda>\<^sub>2m. SP (PR_CONST (op_ASSUME_sorry_bind I))$m"
  apply (rule eq_reflection)
  by auto

lemma hn_ASSUME_sorry_bind[sepref_comb_rules]: (* Dangerous! Allows to assume anything without check! *)
  assumes "I \<Longrightarrow> hn_refine \<Gamma> c \<Gamma>' R CP m"
  shows "hn_refine \<Gamma> c \<Gamma>' R CP (PR_CONST (op_ASSUME_sorry_bind I)$m)"
proof -
  have "sepref_sorry_that I" using sepref_sorry .
  hence "I" unfolding sepref_sorry_that_def by simp
  thus ?thesis using assms by simp
qed


subsection \<open>Big Int Abstraction Distrib. Properties\<close>

lemma big_int_to_nat_tail: "big_int_\<alpha> (tl ai) = (big_int_\<alpha> ai) div limb_sz"
proof (cases ai)
  case Nil
  then show ?thesis by simp
next
  case (Cons a list)
  have tl: "tl ai = list" 
    unfolding Cons by simp
  have "big_int_\<alpha> ai = limb_nat a + limb_sz * big_int_\<alpha> list"
    unfolding Cons by simp
  hence "(big_int_\<alpha> ai) div limb_sz = (limb_nat a + limb_sz * big_int_\<alpha> list) div limb_sz"
    by simp
  also have "... = (limb_nat a) div limb_sz + big_int_\<alpha> list"
    using limb_sz_gt(1) by fastforce
  finally show ?thesis unfolding tl using limb_nat_lt by auto
qed

lemma big_int_to_nat_drop: "big_int_\<alpha> (drop i ai) = (big_int_\<alpha> ai) div (limb_sz ^ i)"
  apply (induction i arbitrary: ai)
  subgoal by simp
  unfolding drop_Suc
  using big_int_to_nat_tail
  by (simp add: div_mult2_eq)

lemma big_int_to_nat_zeros: "big_int_\<alpha> (replicate n 0) = 0"
  by (induction n; auto)

lemma big_int_to_nat_append: "big_int_\<alpha> (ls1 @ ls2) = (big_int_\<alpha> ls1) + (big_int_\<alpha> ls2) * (limb_sz ^ length ls1)"
  apply (induction ls1)
  by (auto simp: distrib_left mult.commute)

lemma big_int_to_nat_snoc: "big_int_\<alpha> (ls1 @ [x]) = big_int_\<alpha> ls1 + limb_nat x * limb_sz ^ length ls1"
  unfolding big_int_to_nat_append by simp

lemma big_int_to_nat_take: "big_int_\<alpha> (take i ai) = (big_int_\<alpha> ai) mod (limb_sz ^ i)"
proof (cases "i \<le> length ai")
  case True
  define l1 l2 where "l1 = take i ai" and "l2 = drop i ai"
  
  have l1len: "length l1 = i" using True l1_def by auto

  have "ai = l1 @ l2" using l1_def l2_def by auto
  hence "big_int_\<alpha> ai = big_int_\<alpha> l1 + big_int_\<alpha> l2 * (limb_sz ^ length l1)"
    using big_int_to_nat_append by simp
  also have "... = big_int_\<alpha> l1 + ((big_int_\<alpha> ai) div (limb_sz ^ i)) * (limb_sz ^ length l1)"
    using big_int_to_nat_drop l2_def by auto
  also have "... = big_int_\<alpha> l1 + ((big_int_\<alpha> ai) div (limb_sz ^ i)) * (limb_sz ^ i)"
    using l1len by simp
  finally show ?thesis using mod_div_mult_eq
    by (metis l1_def nat_diff_add)
next
  case False
  hence "i > length ai" by auto
  hence "limb_sz ^ i > limb_sz ^ (length ai)" 
    using limb_sz_gt power_strict_increasing by blast
  hence gt: "limb_sz ^ i > big_int_\<alpha> ai" using big_int_to_nat_lt 
    using dual_order.strict_trans by blast
  have eq: "take i ai = ai" using False by auto
  show ?thesis unfolding eq using gt by simp
qed

lemma big_int_to_nat_Suc: "big_int_to_nat (take (Suc n) list) = big_int_to_nat (take n list) + limb_nat (get_or_zero list n) * limb_sz ^ n"
	unfolding get_or_zero_def
  apply (cases "Suc n \<le> length list")
  apply simp+
  subgoal 
	proof - 
		assume n_lt: "Suc n \<le> length list"
		hence "big_int_to_nat (take (Suc n) list) = big_int_to_nat ((take n list) @ [list ! n])" 
		  by (simp add: take_Suc_conv_app_nth)
    also have "... = big_int_to_nat (take n list) + limb_nat (list ! n) * limb_sz ^ (length (take n list))" 
      using big_int_to_nat_append by auto
    finally 
		  show ?thesis using n_lt by auto
	qed
	by (auto)

lemma big_int_to_nat_but_last: "list \<noteq> [] \<Longrightarrow> 
  big_int_to_nat list = 
  big_int_to_nat (butlast list) 
  + limb_nat (last list) * limb_sz ^ (length list - 1)"
proof - 
  assume "list \<noteq> []"
  hence 1: "list = butlast list @ [last list]" using append_butlast_last_id by auto
  then obtain xs x where 2: "xs = butlast list" and 3: "x = last list" by simp
  hence "list = xs @ [x]" using 1 by auto
  hence "big_int_to_nat list = big_int_to_nat xs + limb_nat x * limb_sz ^ (length xs)" using big_int_to_nat_append by auto
  then show ?thesis using 2 3 by auto
qed

subsection \<open>Big Int Invar Properties\<close>

lemma big_int_invar_empty[simp]: "big_int_invar []" unfolding big_int_invar_def by auto

lemma big_int_invar_cons: "\<lbrakk>xs = [] \<Longrightarrow> x \<noteq> 0; big_int_invar xs\<rbrakk> \<Longrightarrow> big_int_invar (x # xs)" "big_int_invar (x # xs) \<Longrightarrow> big_int_invar xs"
	unfolding big_int_invar_def by auto


lemma nat_to_big_int_not_empty: "n \<noteq> 0 \<Longrightarrow> last (big_int_\<gamma> n) \<noteq> 0"
	apply (induction n rule: nat_to_big_int.induct)
	subgoal by simp
	subgoal for n
	proof (cases "Suc n < limb_sz")
		case True
		hence "nat_to_big_int (Suc n) = [nat_limb (Suc n)]" by auto
		hence "last (nat_to_big_int (Suc n)) = nat_limb (Suc n)" by auto
		then show ?thesis using True nat_limb_def limb_sz_def limb_wd_def More_Word.of_nat_0 nat.discI by metis 
	next
		assume IH: "Suc n div limb_sz \<noteq> 0 \<Longrightarrow> last (nat_to_big_int (Suc n div limb_sz)) \<noteq> 0"
		case False
		hence "Suc n div limb_sz > 0" 
		by (metis Euclidean_Rings.div_eq_0_iff nat_gtZ_or_Z not_less_zero limb_sz_gt(2))
		hence last: "last (nat_to_big_int (Suc n div limb_sz)) \<noteq> 0" using IH by auto
		have "nat_to_big_int (Suc n) = (nat_limb (Suc n)) # nat_to_big_int (Suc n div limb_sz)"
			using nat_to_big_int.simps(2) by blast
		hence "last (nat_to_big_int (Suc n)) = last (nat_to_big_int (Suc n div limb_sz))"
			using last \<open>0 < Suc n div limb_sz\<close> gr0_conv_Suc by force
		then show ?thesis using last by auto
	qed
	done

lemma nat_to_big_int_invar: "big_int_invar (big_int_\<gamma> n)"
	apply (cases n)
	subgoal by auto
	subgoal for x proof - 
		assume "n = Suc x" 
		hence "n \<noteq> 0" by auto
		hence "last (big_int_\<gamma> n) \<noteq> 0" using nat_to_big_int_not_empty by auto
		then show ?thesis using big_int_invar_def by auto
	qed
	done

lemma big_int_to_nat_0_impl: "big_int_\<alpha> xs = 0 \<Longrightarrow> \<exists>n. xs = replicate n 0"
  proof (induction xs rule: big_int_to_nat.induct)
    case 1
    then show ?case by simp
  next
    case (2 x xs)
    assume IH: "big_int_to_nat xs = 0 \<Longrightarrow> \<exists>n. xs = replicate n 0"
		assume cons_zero: "big_int_to_nat (x # xs) = 0"
		hence "limb_nat x + big_int_to_nat xs * limb_sz = 0" by auto
		hence "limb_nat x = 0" and "big_int_to_nat xs = 0" using limb_sz_gt by auto
		hence "x = 0" and "\<exists>n. xs = replicate n 0" using IH unat_eq_0 limb_nat_def by auto
		then obtain n where "xs = replicate n 0" by auto
		hence "(x # xs) = replicate (n+1) 0" using \<open>x = 0\<close> by auto
		thus "\<exists>n. x # xs = replicate n 0" by blast
	qed

lemma big_int_to_nat_0: "big_int_to_nat xs = 0 \<longleftrightarrow> (\<exists>n. xs = replicate n 0)"
	by (auto simp: big_int_to_nat_0_impl big_int_to_nat_zeros)

lemma big_int_to_nat_not0: "xs \<noteq> [] \<Longrightarrow> last xs \<noteq> 0 \<Longrightarrow> big_int_to_nat xs \<noteq> 0"
	by (auto simp: big_int_to_nat_0)

lemma big_int_to_nat_last0: "list \<noteq> [] \<Longrightarrow> last list = 0 \<Longrightarrow> big_int_to_nat list = big_int_to_nat (butlast list)"
  using big_int_to_nat_but_last by simp

lemma nat_to_big_int_inv: "big_int_invar xs \<Longrightarrow> nat_to_big_int (big_int_to_nat xs) = xs"
	apply (induction xs rule: big_int_to_nat.induct)
  apply (simp add: big_int_invar_cons; auto)
	subgoal for x xs proof -
	  assume invar: "big_int_invar (x # xs)"
    hence 1: "big_int_invar xs" using big_int_invar_cons(2) by blast
		assume "(big_int_invar xs \<Longrightarrow> big_int_\<gamma> (big_int_\<alpha> xs) = xs)"
    hence IH: "big_int_\<gamma> (big_int_\<alpha> xs) = xs" using 1 by auto

    note invar
		hence "last (x # xs) \<noteq> 0" using big_int_invar_def by auto
		hence "(xs = [] \<longrightarrow> x \<noteq> 0) \<and> (xs \<noteq> [] \<longrightarrow> last xs \<noteq> 0)" by (cases xs; auto)
		hence "(xs = [] \<longrightarrow> unat x \<noteq> 0) \<and> (xs \<noteq> [] \<longrightarrow> big_int_to_nat xs \<noteq> 0)"
			using unat_gt_0 big_int_to_nat_not0 by blast
		hence "unat x \<noteq> 0 \<or> big_int_to_nat xs \<noteq> 0" by auto
		hence not_zero: "(unat x + big_int_to_nat xs * limb_sz) \<noteq> 0" using limb_sz_gt
		  by (simp add: limb_mx_suc(2))
		then obtain m where m_def: "m = unat x + big_int_to_nat xs * limb_sz" by auto
		hence "m \<noteq> 0" using not_zero m_def by auto
		then obtain n where "m = Suc n" using nat.exhaust_sel by blast
		hence bint_\<gamma>_not0: "nat_to_big_int m = nat_limb m # nat_to_big_int (m div limb_sz)" 
			by (metis nat_to_big_int.simps(2))
		hence "m mod limb_sz = limb_nat x \<and> m div limb_sz = big_int_to_nat xs"
			using unat_le limb_sz_gt m_def limb_nat_def limb_nat_lt mod_less 
			by (simp add: limb_sz_def)
		hence "nat_to_big_int m = (nat_limb (limb_nat x) # nat_to_big_int (big_int_to_nat xs))" 
			using bint_\<gamma>_not0
			by (metis Word.unat_of_nat nat_limb_def limb_sz_unfold word_unat.Rep_inverse)
		then show ?thesis using m_def IH
		  by (simp add: limb_nat_def mult.commute nat_limb_def)
	qed
	done

subsection \<open>Big Int Relation Properties\<close>

lemma big_int_to_nat_unique: "\<lbrakk> big_int_invar bw; big_int_invar bw'; big_int_to_nat bw = big_int_to_nat bw'\<rbrakk> \<Longrightarrow> bw=bw'"  
	by (metis nat_to_big_int_inv)

lemma big_int_rel_unique:
	"(ai, a) \<in> big_int_rel \<Longrightarrow> (bi, b) \<in> big_int_rel \<Longrightarrow> (a = b \<longleftrightarrow> ai = bi)"
	unfolding big_int_rel_def in_br_conv
	using big_int_to_nat_unique
	by auto

lemma big_int_to_nat_gt: "ai \<noteq> [] \<Longrightarrow> last ai \<noteq> 0 \<Longrightarrow> big_int_to_nat ai \<ge> limb_sz ^ (length ai - 1)"
	apply (induction rule: big_int_to_nat.induct)
  subgoal by simp
	subgoal for x xs
    apply (cases xs)
    subgoal by (simp add: Suc_le_eq limb_nat_def unat_gt_0)
    subgoal for y ys
      apply simp
      by (simp add: trans_le_add2)
    done
  done

lemma big_int_rel_bounds: 
	"(ai, a) \<in> big_int_rel \<Longrightarrow> a < limb_sz ^ (length ai)"
	"(ai, a) \<in> big_int_rel \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> a \<ge> limb_sz ^ (length ai - 1)"
	unfolding big_int_rel_def big_int_invar_def br_def
	subgoal by (auto simp: big_int_to_nat_lt)
	apply clarsimp
	using big_int_to_nat_gt[of "ai"]
	by (metis One_nat_def big_int_to_nat.simps(1) less_not_refl)

lemma replicate0_to_nat: "big_int_to_nat (replicate n 0) = 0"
  by (induction n; auto)

definition "size_log \<equiv> floorlog limb_sz"

lemma size_log_compute: "size_log x = (if x = 0 then 0 else 1 + size_log (x div limb_sz))"
  unfolding size_log_def
  using compute_floorlog limb_sz_gt
  by (metis add.commute bot_nat_0.not_eq_extremum)

lemma size_log_0[simp]: "size_log 0 = 0"
  unfolding size_log_def
  by (simp add: floorlog_eq_zero_iff)

lemma size_log_pow_lt: "a < limb_sz ^ (size_log a)"
	unfolding size_log_def
	using floorlog_leD limb_sz_unfold by force

lemma size_log_pow: "size_log (limb_sz ^ n) = n + 1"
  apply (induction n)
  subgoal using limb_sz_unfold size_log_compute by simp
  subgoal for n using size_log_compute[of "limb_sz ^ Suc n"]
    limb_sz_unfold by auto
  done
  
lemma size_pow: "size_log (limb_sz ^ size_log a) = size_log a + 1"
	using size_log_pow by auto 

lemma size_log_mod: "a mod limb_sz ^ (size_log a) = a"
	using size_log_pow_lt by auto

lemma big_int_rel_length_log: "(ai, a) \<in> big_int_rel \<Longrightarrow> length ai = size_log a" 
	unfolding big_int_rel_def in_br_conv size_log_def
	apply (induction arbitrary: a rule: big_int_to_nat.induct)
	subgoal using floorlog_def by auto
	apply clarsimp
	subgoal for x xs proof -
		have 1: "limb_nat x < limb_sz" using limb_nat_lt by auto

		assume IH: "big_int_invar xs \<Longrightarrow> length xs = floorlog limb_sz (big_int_\<alpha> xs)"
		assume invar: "big_int_invar (x # xs)"
		hence "big_int_invar xs" using big_int_invar_cons by auto
		hence "length xs = floorlog limb_sz (big_int_\<alpha> xs)" using IH by auto
		hence 2: "Suc (length xs) = floorlog limb_sz (big_int_\<alpha> xs) + 1" by auto

		have "limb_nat x + big_int_\<alpha> xs * limb_sz > 0" using invar big_int_to_nat_not0 big_int_invar_def limb_nat_def
		  by (metis big_int_to_nat.simps(2) list.distinct(1) mult.commute not_gr_zero)

		hence "floorlog limb_sz (limb_nat x + big_int_\<alpha> xs * limb_sz) = floorlog limb_sz (big_int_\<alpha> xs) + 1"
		using compute_floorlog limb_sz_gt(1) 1 by simp
		thus ?thesis using 2 by (simp add: mult.commute)
	qed
	done

lemma big_int_rel_size_leq: "(ai, a) \<in> big_int_rel \<Longrightarrow> (a < limb_sz ^ l) \<longleftrightarrow> (length ai \<le> l)"
  unfolding big_int_rel_length_log
  using size_log_pow_lt
  using floorlog_le_iff limb_sz_gt(1) size_log_def by presburger

lemma big_int_\<alpha>_length_gt2: "big_int_\<alpha> ai \<ge> limb_sz \<Longrightarrow> length ai \<ge> 2"
proof (cases "length ai \<ge> 2")
	case True
	then show ?thesis by simp
next
	assume assm: "big_int_\<alpha> ai \<ge> limb_sz"
	case False
	hence "length ai < 2" by simp
	hence "length ai \<le> 1" by simp
	hence "limb_sz ^ length ai \<le> limb_sz"
		by (metis limb_sz_gt(1) power_increasing_iff power_one_right)
	hence "big_int_\<alpha> ai < limb_sz" using big_int_to_nat_lt
		using order.strict_trans2 by blast
	then show ?thesis using assm by simp
qed

subsection \<open>Big Int List Operations\<close>


definition big_int_length :: "big_int \<Rightarrow> nat" where "big_int_length ai \<equiv> length ai" 

lemma big_int_length_correct: "big_int_invar ai \<Longrightarrow> big_int_length ai = size_log (big_int_\<alpha> ai)"
	by (simp add: big_int_length_def big_int_rel_def big_int_rel_length_log in_br_conv)

(* TODO: use this instead of last when working with big_ints *)
definition big_int_last_limb :: "big_int \<Rightarrow> limb" where "big_int_last_limb ai \<equiv> last ai"

lemma big_int_length_pow_gt: "(ai, a) \<in> big_int_rel \<Longrightarrow> a < limb_sz ^ (big_int_length ai)"
  using big_int_length_def big_int_rel_bounds(1) by presburger

lemma big_int_length_pow_lt: "(ai, a) \<in> big_int_rel \<Longrightarrow> a > 0 \<Longrightarrow> a \<ge> limb_sz ^ (big_int_length ai - 1)"
  using big_int_length_def big_int_rel_bounds(2) by force

definition big_int_but_last :: "big_int \<Rightarrow> big_int"
  where "big_int_but_last \<equiv> butlast"

term "mop_list_butlast"

(* Note: The input does not need to satisfy the invariant *)
definition big_int_trim :: "big_int \<Rightarrow> big_int nres"
	where "big_int_trim ai \<equiv> do {
		bi \<leftarrow> WHILEIT 
				(\<lambda>bi. big_int_to_nat bi = big_int_to_nat ai) 
				(\<lambda>bi. big_int_length bi > 0 \<and> big_int_last_limb bi = 0)
				\<comment> \<open>(\<lambda>bi. RETURN (butlast bi))\<close>
        mop_list_butlast
				ai;
		RETURN bi
}"

term "get_or_zero"
term "WHILEIT"
term "FOREACHoci (\<lambda>a b. a > b)"

definition bi_append :: "big_int \<Rightarrow> limb \<Rightarrow> big_int nres" where
  "bi_append xi z \<equiv> do {
    ASSUME (sepref_sorry_that(length xi+1 < max_snat 64));
    ASSERT(length xi + 1 < max_snat 64);
    RETURN (xi @ [z])
  }"

(*
  (moved) TODO: there should be bi_append_correct lemma!
  There is no refinement since invariant is not in precondition or postcondition
 *)
lemma bi_append_correct: "bi_append ai x \<le> SPEC (\<lambda> xs. xs = ai @ [x])"
  unfolding bi_append_def
  apply (refine_vcg)
  by (simp_all add: sepref_sorry)

subsubsection \<open>Comparison operator \<open>\<le>\<close> and operators \<open>\<ge>\<close> \<open><\<close> \<open>>\<close> in terms of \<open>\<le>\<close> \<close>

definition big_int_leq :: "big_int \<Rightarrow> big_int \<Rightarrow> bool nres" 
  where "big_int_leq ai bi \<equiv> do {
    let la = big_int_length ai;
    let lb = big_int_length bi;
    if la = lb 
    then do {
      ASSERT (lb = la);
      if la \<ge> 1 
        then do {
          ASSERT (la \<ge> 1);
          let idx = la - 1;
          idx \<leftarrow> WHILEIT
            (\<lambda> idx . (drop (idx + 1) ai = drop (idx + 1) bi))
            \<comment> \<open>TODO: remove dynamic index check\<close> 
            (\<lambda> idx . (get_or_zero ai idx = get_or_zero bi idx) \<and> idx \<ge> 1)
            (\<lambda> idx . do {
              ASSERT (idx \<ge> 1);
              let idx = idx - 1;
              RETURN idx
            }) (idx);
          let aix = get_or_zero ai idx;
          let bix = get_or_zero bi idx;
          let res = aix \<le> bix;
          RETURN res
        }
        else RETURN True 
      }
    else RETURN (la < lb) 
  }"

definition big_int_gt :: "big_int \<Rightarrow> big_int \<Rightarrow> bool nres" 
  where "big_int_gt ai bi \<equiv> do {
    leq \<leftarrow> big_int_leq ai bi;
    let gt = \<not> leq;
    RETURN gt
  }"

definition big_int_geq :: "big_int \<Rightarrow> big_int \<Rightarrow> bool nres" 
  where "big_int_geq ai bi \<equiv> big_int_leq bi ai"

definition big_int_lt :: "big_int \<Rightarrow> big_int \<Rightarrow> bool nres" 
  where "big_int_lt ai bi \<equiv> do {
    geq \<leftarrow> big_int_geq ai bi;
    let lt = \<not> geq;
    RETURN lt
}"

lemma big_int0_inj: "([], a) \<in> big_int_rel \<Longrightarrow> a = 0"
  using big_int0_def big_int_rel_unique big_int_zero_refine by presburger

lemma "drop (Suc idx) ai = drop (Suc idx) bi \<Longrightarrow> hd (drop idx ai) = hd (drop idx bi) \<Longrightarrow> drop idx ai = drop idx bi"
  unfolding Cons_nth_drop_Suc
  oops

lemma drop1_tail: "drop (Suc 0) ai = tl ai"
  by (simp add: drop_Suc)

lemma get_head: "ai \<noteq> [] \<Longrightarrow> get_or_zero ai 0 = hd ai"
  unfolding get_or_zero_def
  by (simp add: hd_conv_nth)

lemma tl_hd_eq: "ai \<noteq> [] \<Longrightarrow> bi \<noteq> [] \<Longrightarrow> tl ai = tl bi \<Longrightarrow> hd ai = hd bi \<Longrightarrow> ai = bi"
  by (meson list.expand)

lemma leq_m: "a \<noteq> b \<Longrightarrow> (m :: nat) > 0 \<Longrightarrow> x < m \<Longrightarrow> y < m \<Longrightarrow> (a \<le> b) \<longleftrightarrow> (a * m + x) \<le> (b * m + y)"
  by (metis le_eq_less_or_eq linorder_not_less mlex_fst_decrI)

lemma big_int_leq_correct: "(ai, a) \<in> big_int_rel \<Longrightarrow> (bi, b) \<in> big_int_rel \<Longrightarrow> big_int_leq ai bi \<le> (\<Down> Id) (RETURN (a \<le> b))"
  unfolding big_int_leq_def big_int_length_def
  apply refine_vcg
  subgoal by simp
  apply (rule wf_measure[where f="\<lambda>idx. idx"])


  subgoal unfolding big_int_length_def by simp
  subgoal by simp

  (* Invar \<and> Cond \<Rightarrow> Next Invar *)
  subgoal for idx 
    apply (cases "idx < big_int_length ai")
    unfolding big_int_length_def get_or_zero_def
    using Cons_nth_drop_Suc[of idx ai, symmetric] Cons_nth_drop_Suc[of idx bi, symmetric]
    by auto
  
  subgoal for idx by force

  subgoal for idx 
    unfolding big_int_length_def big_int_rel_def in_br_conv 
    apply (cases "bi = []")
    apply simp
    apply (cases "get_or_zero ai idx = get_or_zero bi idx")
    apply (cases "idx = 0")
    
    apply (clarsimp simp: drop1_tail get_head)
    subgoal using tl_hd_eq[of ai bi] by fastforce
    apply simp
    apply (cases "idx \<ge> length ai")
    unfolding get_or_zero_def
    subgoal by simp
    apply clarsimp
    subgoal proof -
      assume eq_len: "length bi = length ai"

      assume "ai ! idx \<noteq> bi ! idx" 
      hence different: "limb_nat (ai ! idx) \<noteq> limb_nat (bi ! idx)"
        by (simp add: limb_nat_def word_unat_eq_iff)

      have limb_nat_compare: "ai ! idx \<le> bi ! idx \<longleftrightarrow> limb_nat (ai ! idx) \<le> limb_nat (bi ! idx)"
        using limb_compare by presburger

      assume "\<not> length ai \<le> idx"
      hence idx_ai: "idx < length ai" by fastforce
      hence idx_bi: "idx < length bi" using eq_len by fastforce

      assume drop_eq: "drop (Suc idx) ai = drop (Suc idx) bi"

      have "ai = take idx ai @ drop idx ai" using idx_ai by simp
      hence "ai = (take idx ai) @ [ai ! idx] @ (drop (Suc idx) ai)" using idx_ai
        by (metis append.assoc append_take_drop_id hd_drop_conv_nth take_hd_drop)
      hence "big_int_\<alpha> ai = big_int_\<alpha> ..." by simp
      hence ai_split: "big_int_\<alpha> ai = big_int_\<alpha> (take idx ai) + (limb_nat (ai ! idx)) * limb_sz ^ idx + big_int_\<alpha> (drop (Suc idx) ai) * limb_sz ^ (Suc idx)"
        using big_int_to_nat_append
        by (metis (no_types, lifting) \<open>ai = take idx ai @ [ai ! idx] @ drop (Suc idx) ai\<close> \<open>ai = take idx ai @ drop idx ai\<close> add.assoc add.commute add_mult_distrib
            big_int0_correct(2) big_int0_def big_int_to_nat.simps(2) big_int_to_nat_drop big_int_to_nat_take div_mod_decomp length_Cons list.size(3) mult.assoc
            mult.right_neutral mult_0_right power_0 power_Suc same_append_eq)

      have take_ai_lt: "big_int_\<alpha> (take idx ai) \<le> limb_sz ^ idx"
        using big_int_to_nat_take limb_sz_gt(1) by auto
      have take_bi_lt: "big_int_\<alpha> (take idx bi) \<le> limb_sz ^ idx"
        using big_int_to_nat_take limb_sz_gt(1) by auto
      have limb_sz_idx_nz: "limb_sz ^ idx > 0" unfolding limb_sz_unfold by presburger


      have "bi = take idx bi @ drop idx bi" using idx_bi by simp
      hence "bi = (take idx bi) @ [bi ! idx] @ (drop (Suc idx) bi)" using idx_bi
        by (metis append.assoc append_take_drop_id hd_drop_conv_nth take_hd_drop)
      hence "big_int_\<alpha> bi = big_int_\<alpha> ..." by simp
      hence bi_split: "big_int_\<alpha> bi = big_int_\<alpha> (take idx bi) + (limb_nat (bi ! idx)) * limb_sz ^ idx + big_int_\<alpha> (drop (Suc idx) bi) * limb_sz ^ (Suc idx)"
        using big_int_to_nat_append
        by (metis (no_types, lifting) \<open>bi = take idx bi @ [bi ! idx] @ drop (Suc idx) bi\<close> \<open>bi = take idx bi @ drop idx bi\<close> add.assoc add.commute add_mult_distrib
            big_int0_correct(2) big_int0_def big_int_to_nat.simps(2) big_int_to_nat_drop big_int_to_nat_take div_mod_decomp length_Cons list.size(3) mult.assoc
            mult.right_neutral mult_0_right power_0 power_Suc same_append_eq)
      
      hence "big_int_\<alpha> ai \<le> big_int_\<alpha> bi \<longleftrightarrow> 
        big_int_\<alpha> (take idx ai) + (limb_nat (ai ! idx)) * limb_sz ^ idx + big_int_\<alpha> (drop (Suc idx) ai) * limb_sz ^ (Suc idx) \<le> 
        big_int_\<alpha> (take idx bi) + (limb_nat (bi ! idx)) * limb_sz ^ idx + big_int_\<alpha> (drop (Suc idx) bi) * limb_sz ^ (Suc idx)" using ai_split bi_split by presburger
      hence "big_int_\<alpha> ai \<le> big_int_\<alpha> bi \<longleftrightarrow> 
        big_int_\<alpha> (take idx ai) + (limb_nat (ai ! idx)) * limb_sz ^ idx \<le> 
        big_int_\<alpha> (take idx bi) + (limb_nat (bi ! idx)) * limb_sz ^ idx" using drop_eq by simp
      also have "... \<longleftrightarrow> (limb_nat (ai ! idx)) \<le> (limb_nat (bi ! idx))"
        using take_ai_lt take_bi_lt different limb_sz_idx_nz leq_m[of "limb_nat (ai ! idx)" "limb_nat (bi ! idx)" "limb_sz ^ idx" "big_int_\<alpha> (take idx ai)" "big_int_\<alpha> (take idx bi)"]
        by (simp add: add.commute big_int_to_nat_take)
      finally show ?thesis using limb_nat_compare by simp
    qed
    done

  subgoal unfolding big_int_length_def proof -
    assume rela: "(ai, a) \<in> big_int_rel" and relb:"(bi, b) \<in> big_int_rel"
    assume len_eq: "length ai = length bi"
    assume not_not_zero: "\<not> 1 \<le> length ai"
    hence "length ai = 0" by force
    hence "length bi = 0" using len_eq by argo
    hence "ai = bi" using \<open>length ai = 0\<close> by fastforce
    hence "a = b" using rela relb
      using big_int_rel_unique by presburger
    thus ?thesis by simp
  qed
  subgoal using big_int_length_pow_gt big_int_length_pow_lt 
    by (smt (verit, best) big_int_length_def big_int_rel_size_leq le_eq_less_or_eq linorder_not_less order_less_trans param_bool(1,2)) 
  done

lemma lt_not_leq_rev: "(b::nat) < a \<longleftrightarrow> \<not> (a \<le> b)"
  by (metis le_def) 

lemma big_int_gt_correct: "(ai, a) \<in> big_int_rel \<Longrightarrow> (bi, b) \<in> big_int_rel \<Longrightarrow> big_int_gt ai bi \<le> (\<Down> Id) (RETURN (a > b))"
  unfolding big_int_gt_def
  apply (refine_vcg)
  apply (clarsimp simp: lt_not_leq_rev)
  using big_int_leq_correct[of ai a bi b]
  by (simp add: RES_sng_eq_RETURN)

lemma leq_geq_rev: "(a::nat) \<ge> b \<longleftrightarrow> b \<le> a"
  by presburger

lemma big_int_geq_correct: "(ai, a) \<in> big_int_rel \<Longrightarrow> (bi, b) \<in> big_int_rel \<Longrightarrow> big_int_geq ai bi \<le> (\<Down> Id) (RETURN (a \<ge> b))"
  unfolding big_int_geq_def
  apply (refine_vcg)
  apply (clarsimp)
  apply (rewrite leq_geq_rev)
  using big_int_leq_correct[of ai a bi b]
  by (metis RES_sng_eq_RETURN big_int_leq_correct refine_IdD)

lemma lt_not_geq_rev: "(b < a) \<longleftrightarrow> \<not> (b::nat) \<ge> a"
  by fastforce

lemma big_int_lt_correct: "(ai, a) \<in> big_int_rel \<Longrightarrow> (bi, b) \<in> big_int_rel \<Longrightarrow> big_int_lt ai bi \<le> (\<Down> Id) (RETURN (a < b))"
  unfolding big_int_lt_def
  apply (refine_vcg)
  apply (rewrite lt_not_geq_rev)
  apply (clarsimp)
  using big_int_leq_correct[of ai a bi b]
  by (metis RES_sng_eq_RETURN big_int_geq_def big_int_leq_correct refine_IdD)


lemma big_int_trim_correct: "big_int_trim ai \<le> SPEC (\<lambda>r. big_int_to_nat r = big_int_to_nat ai \<and> big_int_invar r)"
	unfolding big_int_trim_def big_int_last_limb_def big_int_length_def
	apply refine_vcg
  apply (rule wf_measure[where f="\<lambda>bi. length bi"])
  subgoal by simp
  subgoal by simp
	subgoal by (simp add: big_int_to_nat_last0)
  subgoal by auto
  subgoal unfolding big_int_invar_def by auto
  done


definition remove_last_limb:: "big_int \<Rightarrow> big_int nres"
  where "remove_last_limb ai \<equiv> big_int_trim (butlast ai)"

definition big_int_drop:: "nat \<Rightarrow> big_int \<Rightarrow> big_int nres"
  where "big_int_drop i ai \<equiv> do {
    if i > big_int_length ai
    then RETURN big_int0
    else do {
      ASSERT (i \<le> length ai);
      let r = op_list_drop i ai;
      r \<leftarrow> big_int_trim r;
      RETURN r
  }
}"

definition big_int_take:: "nat \<Rightarrow> big_int \<Rightarrow> big_int nres"
  where "big_int_take i ai \<equiv> do {
    if i > big_int_length ai 
    then RETURN ai
    else do {
      ASSERT (i \<le> length ai);
      let l = op_list_take i ai;
      l \<leftarrow> big_int_trim l;
      RETURN l
  }
}"


lemma big_int_drop_correct: "(ai, a) \<in> big_int_rel \<Longrightarrow> big_int_drop m ai \<le> \<Down> big_int_rel (RETURN (a div (limb_sz ^ m)))"
	unfolding big_int_drop_def
	using big_int_rel_bounds
	apply (refine_vcg big_int_trim_correct)
	unfolding big_int_rel_def in_br_conv
	apply (metis Euclidean_Rings.div_less big_int0_correct(1,2) big_int_length_correct floorlog_le_iff less_le_not_le limb_sz_gt(1) size_log_def)
  subgoal unfolding big_int_length_def by simp
	by (auto simp: big_int_to_nat_drop)

lemma big_int_drop_correct_eq: "m = n \<Longrightarrow> (ai, a) \<in> big_int_rel \<Longrightarrow> big_int_drop m ai \<le> \<Down> big_int_rel (RETURN (a div (limb_sz ^ n)))"
	using big_int_drop_correct by simp

lemma big_int_drop_correct': "(ai, a) \<in> big_int_rel \<Longrightarrow> big_int_drop m ai \<le> (SPEC (\<lambda> c. (c, a div (limb_sz ^ m)) \<in> big_int_rel))"
	using big_int_drop_correct 
	by (simp add: conc_fun_RETURN)


lemma big_int_take_correct: "(ai, a) \<in> big_int_rel \<Longrightarrow> big_int_take m ai \<le> \<Down> big_int_rel (RETURN (a mod (limb_sz ^ m)))"
	unfolding big_int_take_def
  using big_int_rel_bounds
	apply (refine_vcg big_int_trim_correct)
	unfolding big_int_rel_def in_br_conv
	  apply (metis big_int_length_correct size_log_def floorlog_le_iff limb_sz_gt(1) less_le_not_le mod_less)
  subgoal unfolding big_int_length_def by simp
	by (auto simp: big_int_to_nat_take)

lemma big_int_take_correct_eq: "m = n \<Longrightarrow> (ai, a) \<in> big_int_rel \<Longrightarrow> big_int_take m ai \<le> \<Down> big_int_rel (RETURN (a mod (limb_sz ^ n)))"
	using big_int_take_correct by simp

lemma big_int_take_correct': "(ai, a) \<in> big_int_rel \<Longrightarrow> big_int_take m ai \<le> (SPEC (\<lambda> c. (c, a mod (limb_sz ^ m)) \<in> big_int_rel))"
	using big_int_take_correct
	by (simp add: conc_fun_RETURN)

definition big_int_rshift :: "nat \<Rightarrow> big_int \<Rightarrow> big_int nres"
  where "big_int_rshift m ai \<equiv> big_int_trim ((replicate m 0) @ ai)"

lemma big_int_to_nat_butlast: "big_int_\<alpha> (butlast ai) = big_int_\<alpha> ai mod limb_sz ^ (length ai - Suc 0)"
	apply (induction ai)
	by (auto simp flip: take_butlast_conv simp: big_int_to_nat_take)

lemma remove_last_limb_correct: "(ai,a)\<in>big_int_rel \<Longrightarrow> 
	remove_last_limb ai \<le> SPEC (\<lambda>r. (r,a mod limb_sz ^(size_log a - 1)) \<in> big_int_rel)"
	unfolding remove_last_limb_def 
	apply (refine_vcg big_int_trim_correct)
	unfolding big_int_rel_def in_br_conv
	using big_int_to_nat_butlast big_int_rel_length_log
	by (metis One_nat_def big_int_rel_def in_br_conv)

lemma big_int_rshift_correct: "(ai, a) \<in> big_int_rel	\<Longrightarrow> big_int_rshift m ai \<le> \<Down> big_int_rel (RETURN (a * limb_sz ^ m))"
	unfolding big_int_rshift_def
	apply (refine_vcg big_int_trim_correct)
	unfolding big_int_rel_def in_br_conv big_int_to_nat_append replicate0_to_nat
	by auto

lemma big_int_rshift_correct_eq: "m = n \<Longrightarrow> (ai, a) \<in> big_int_rel	\<Longrightarrow> big_int_rshift m ai \<le> \<Down> big_int_rel (RETURN (a * limb_sz ^ n))"
	using big_int_rshift_correct by simp

lemma big_int_rshift_correct_sqr: "(ai, a) \<in> big_int_rel	\<Longrightarrow> big_int_rshift (2*m) ai \<le> \<Down> big_int_rel (RETURN (a * (limb_sz ^ m)\<^sup>2))"
	using big_int_rshift_correct
	by (metis power_even_eq)

lemma big_int_rshift_correct_sqr_eq: "m = n \<Longrightarrow> (ai, a) \<in> big_int_rel	\<Longrightarrow> big_int_rshift (2*m) ai \<le> \<Down> big_int_rel (RETURN (a * (limb_sz ^ n)\<^sup>2))"
	using big_int_rshift_correct_sqr
	by simp

lemma big_int_shift_correct'[refine]: "(ai, a) \<in> big_int_rel	\<Longrightarrow> big_int_rshift m ai \<le>  (SPEC (\<lambda> c. (c, a * limb_sz ^ m) \<in> big_int_rel))"
	unfolding big_int_rshift_def
	apply (refine_vcg big_int_trim_correct)
	unfolding big_int_rel_def in_br_conv
	by (auto simp: big_int_to_nat_append replicate0_to_nat)


subsubsection \<open>Big Int Addition\<close>

definition big_int_add_cond :: "big_int \<Rightarrow> big_int \<Rightarrow> (big_int \<times> nat \<times> limb) \<Rightarrow> bool"
where "big_int_add_cond ai bi = (
	\<lambda>(ci, idx, cr). idx < max (length ai) (length bi) \<or> (cr > 0)
)"

definition big_int_add_loop_invar :: "big_int \<Rightarrow> big_int \<Rightarrow> limb \<Rightarrow> (big_int \<times> nat \<times> limb) \<Rightarrow> bool"
where "big_int_add_loop_invar ai bi init_cr = (
	\<lambda>(ci, idx, cr). 
  cr \<in> {0, 1}
  \<and> idx = length ci
	\<and> idx < max (length ai) (length bi) + 2
	\<and> big_int_to_nat (take idx ai) + big_int_to_nat (take idx bi) + limb_nat init_cr = big_int_to_nat ci + limb_nat cr * limb_sz ^ idx
)"


definition big_int_add_loop :: "big_int \<Rightarrow> big_int \<Rightarrow> limb \<Rightarrow> big_int nres"
  where "big_int_add_loop ai bi init_cr \<equiv> do {
      (ci, _, _) \<leftarrow> WHILEIT 
        (big_int_add_loop_invar ai bi init_cr)
        (big_int_add_cond ai bi)
			(\<lambda> (ci, idx, cr) . do {
				let ai = get_or_zero ai idx;
				let bi = get_or_zero bi idx;
				let (r, cr) = add_carry ai bi cr;
        
        ci_next \<leftarrow> bi_append ci r;
        ASSERT (idx+1 \<le> length ci_next);
        
        let idx = idx + 1;

				RETURN (ci_next, idx, cr)
			}) (big_int0, 0, init_cr);
      RETURN ci
}"

lemma big_int_add_loop_correct: "(ai, a) \<in> big_int_rel \<Longrightarrow> (bi, b) \<in> big_int_rel \<Longrightarrow> init_cr\<in>{0,1} \<Longrightarrow> big_int_add_loop ai bi init_cr \<le> SPEC (\<lambda>ci. big_int_\<alpha> ci = a + b + limb_nat init_cr)"
  unfolding big_int_add_loop_def big_int0_def
  apply (refine_vcg WHILEIT_rule[where R="measure (\<lambda> (ci, idx, cr). max (length ai) (length bi) + 2 - idx)"] bi_append_correct)
  (* wf condition *)
	subgoal by simp
  (* invar initial *)
  subgoal unfolding big_int_add_loop_invar_def by auto

  (* Derived bound-assertion for index *)
  subgoal by (clarsimp simp: big_int_add_cond_def big_int_add_loop_invar_def)

   (* invar preserved *)
  apply (clarsimp simp: big_int_add_cond_def big_int_add_loop_invar_def)
  subgoal for ci cr cidx new_cr
		apply (intro conjI)
    (* Next carry is 0 or 1 *)
    subgoal proof -
      assume "add_carry (get_or_zero ai (length ci)) (get_or_zero bi (length ci)) cr = (cidx, new_cr)"
      hence "new_cr = snd (add_carry (get_or_zero ai (length ci)) (get_or_zero bi (length ci)) cr)" by simp
      thus ?thesis using add_carry_bit by auto
    qed

    (* Index in range *)
    subgoal proof (rule ccontr)
      define idx where idx: "idx = length ci"
      (* Assume otherwise *)
			assume False: "\<not> length ci < Suc (max (length ai) (length bi))"
      (* Invar ci value *)
			assume IH: "(big_int_\<alpha> (take (length ci) ai) + big_int_\<alpha> (take (length ci) bi)) + limb_nat init_cr = big_int_\<alpha> ci + limb_nat cr * limb_sz ^ length ci"
			assume INIT_CR_CASES: "init_cr = 0 \<or> init_cr = 1"
      (* Condition is true *)
		  assume "length ci < max (length ai) (length bi) \<or> 0 < cr"
      (* Carry is set *)
			hence "0 < cr" using word_gt_0 False by auto
			hence "limb_nat cr * limb_sz ^ length ci \<ge> limb_sz ^ idx" using idx 
			  by (simp add: word_less_nat_alt limb_nat_def) 
      (* Bound on ai bi values from below *)
			hence geq: "big_int_to_nat (take idx ai) + big_int_to_nat (take idx bi) + limb_nat init_cr \<ge> limb_sz ^ idx"
				using IH idx by (simp add: trans_le_add2)

			have idx_max: "idx > max (length ai) (length bi)" using idx False by auto
      hence idx_NZ: "idx \<noteq> 0" by auto

			hence 1: "idx > length ai" and 2: "idx > length bi" using idx_max by auto

      (* Bound on ai bi values from above *)
      have A_less: "limb_sz ^ (length ai) \<le> limb_sz ^ (idx - 1)" and 
           B_less: "limb_sz ^ (length bi) \<le> limb_sz ^ (idx - 1)" using 1 2 
        using limb_sz_gt(1) by force+

      (* Combine bounds to get contradiction *)
			have "take idx ai = ai" and "take idx bi = bi" using 1 2 by auto
			hence "big_int_to_nat (take idx ai) + big_int_to_nat (take idx bi) =
				big_int_to_nat ai + big_int_to_nat bi" by auto
      also have "... < limb_sz ^ (length ai) + limb_sz ^ (length bi) " using big_int_to_nat_lt
				using add_less_mono by presburger
			also have "... \<le> limb_sz ^ (idx - 1) + limb_sz ^ (idx - 1) " using A_less B_less by auto
      also have "... = 2 * limb_sz ^ (idx - 1)" by auto
      finally have "limb_sz ^ idx \<le> 2 * limb_sz ^ (idx - 1)" 
        using geq INIT_CR_CASES by auto
      hence "limb_sz * limb_sz ^ (idx - 1) \<le> 2 * limb_sz ^ (idx - 1)"
        using idx_NZ by (metis power_eq_if)
      hence "limb_sz \<le> 2" using limb_sz_gt by fastforce
			thus "False" using limb_sz_gt by simp
		qed 
    subgoal
    proof -
      assume "cr = 0 \<or> cr = 1"
      hence cr: "cr \<in> {0, 1}" by auto
			define idx where idx: "idx = length ci"
			assume step: "add_carry (get_or_zero ai (length ci)) (get_or_zero bi (length ci)) cr = (cidx, new_cr)"
                                     
			define sum where "sum = limb_nat (get_or_zero ai (length ci)) + limb_nat (get_or_zero bi (length ci)) + limb_nat cr"
			hence cidx: "cidx = nat_limb (sum mod limb_sz)" using step cr add_carry_correct add_carry_sum
			  by (metis fst_conv limb_nat_id(2))
			have next_cr: "new_cr = nat_limb (sum div limb_sz)" using step cr add_carry_correct add_carry_sum
			  by (metis limb_nat_id(2) sum_def snd_conv)

			have sum: "sum = limb_nat cidx + limb_nat new_cr * limb_sz" 
        using cr step sum_def add_carry_sum
        by auto

			assume IH: "big_int_\<alpha> (take (length ci) ai) + big_int_\<alpha> (take (length ci) bi) + limb_nat init_cr  = big_int_to_nat ci + limb_nat cr * limb_sz ^ length ci"
			hence "big_int_to_nat ai mod limb_sz ^ idx + big_int_to_nat bi mod limb_sz ^ idx + limb_nat init_cr = big_int_to_nat ci + limb_nat cr * limb_sz ^ idx"
				using big_int_to_nat_take idx by auto

			have ai_next:"big_int_to_nat (take (Suc idx) ai) = big_int_to_nat (take idx ai) + limb_nat (get_or_zero ai idx) * limb_sz ^ idx"
				using big_int_to_nat_Suc by auto

			have bi_next:"big_int_to_nat (take (Suc idx) bi) = big_int_to_nat (take idx bi) + limb_nat (get_or_zero bi idx) * limb_sz ^ idx"
				using big_int_to_nat_Suc by auto

			have "big_int_to_nat (take (Suc idx) ai) + big_int_to_nat (take (Suc idx) bi) = 
			 	  big_int_to_nat (take idx ai) + limb_nat (get_or_zero ai idx) * limb_sz ^ idx
			 +  big_int_to_nat (take idx bi) + limb_nat (get_or_zero bi idx) * limb_sz ^ idx " using ai_next bi_next by auto
      also have "... = 
				big_int_to_nat (take idx ai) + big_int_to_nat (take idx bi) 
      + (limb_nat (get_or_zero ai idx) + limb_nat (get_or_zero bi idx)) * limb_sz ^ idx"
        using add_mult_distrib by presburger	
		  finally have "(big_int_to_nat (take (Suc idx) ai) + big_int_to_nat (take (Suc idx) bi)) + limb_nat init_cr = 
				big_int_to_nat ci + limb_nat cr * limb_sz ^ idx + (limb_nat (get_or_zero ai idx) + limb_nat (get_or_zero bi idx)) * limb_sz ^ idx"
				using IH idx by auto
      also have "... =
				big_int_to_nat ci + (limb_nat cr + limb_nat (get_or_zero ai idx) + limb_nat (get_or_zero bi idx)) * limb_sz ^ idx" using add_mult_distrib by presburger
			also have "... =
				big_int_to_nat ci + sum * limb_sz ^ idx" using sum_def idx by auto
			also have "... = 
				big_int_to_nat ci + (limb_nat cidx + limb_nat new_cr * limb_sz) * limb_sz ^ idx " using sum_def step sum
				by argo
			also have "...= 
				big_int_to_nat ci + (limb_nat cidx) * limb_sz ^ idx + (limb_nat new_cr) * limb_sz * limb_sz ^ idx" using add_mult_distrib by presburger
			also have "... = 
				big_int_to_nat (ci @ [cidx]) + limb_nat new_cr * limb_sz * limb_sz ^ idx" using big_int_to_nat_append by (simp add: idx)
      finally show ?thesis using idx by auto
		qed
		done

	subgoal for ci idx cr cidx next_cr
    unfolding big_int_add_loop_invar_def
    by (clarsimp; linarith)	
  subgoal for ci idx cr 
		apply (unfold big_int_rel_def br_def big_int_add_loop_invar_def big_int_add_cond_def big_int_invar_def)
		apply (cases "cr=0"; simp add: word_gt_0)
		by auto 
  done


definition big_int_add :: "big_int \<Rightarrow> big_int \<Rightarrow> big_int nres"
	where "big_int_add ai bi \<equiv> do {
	  let init_cr = 0; 
		ci \<leftarrow> big_int_add_loop ai bi init_cr;
		ci \<leftarrow> big_int_trim ci;
    RETURN ci	
	}"

(* Fused add and increment *)
definition big_int_add_inc :: "big_int \<Rightarrow> big_int \<Rightarrow> big_int nres"
  where "big_int_add_inc ai bi \<equiv> do {
    let init_cr = 1;
		ci \<leftarrow> big_int_add_loop ai bi init_cr;
    ci \<leftarrow> big_int_trim ci;
		RETURN ci
	}"

lemma big_int_add_correct: "(ai, a) \<in> big_int_rel \<Longrightarrow> (bi, b) \<in> big_int_rel \<Longrightarrow> big_int_add ai bi \<le> \<Down>big_int_rel (RETURN (a + b))"
  apply (unfold big_int_add_def)
  apply (refine_vcg big_int_add_loop_correct big_int_trim_correct)
  apply assumption
  apply assumption
  apply simp          
  subgoal unfolding big_int_rel_def in_br_conv by simp
  done

lemma big_int_add_correct': "(ai, a) \<in> big_int_rel \<Longrightarrow> (bi, b) \<in> big_int_rel \<Longrightarrow> big_int_add ai bi \<le> SPEC (\<lambda> ci. (ci, a + b) \<in> big_int_rel)"
  using big_int_add_correct
  by (simp add: conc_fun_RETURN)

lemma big_int_add_inc_correct: 
  "(ai, a) \<in> big_int_rel \<Longrightarrow> (bi, b) \<in> big_int_rel \<Longrightarrow> big_int_add_inc ai bi \<le> \<Down>big_int_rel (RETURN (a + b + 1))"
  apply (unfold big_int_add_inc_def)
  apply (refine_vcg big_int_add_loop_correct big_int_trim_correct)
  apply assumption
  apply assumption
  apply simp
  subgoal unfolding big_int_rel_def in_br_conv by simp
  done

lemma big_int_add_inc_correct': 
  "(ai, a) \<in> big_int_rel \<Longrightarrow> (bi, b) \<in> big_int_rel \<Longrightarrow> big_int_add_inc ai bi \<le> SPEC (\<lambda> ci. (ci, a + b + 1) \<in> big_int_rel)"
  using big_int_add_inc_correct
  by (simp add: conc_fun_RETURN)

subsubsection \<open>Big Int Subtraction\<close>

definition "compl_invar ai l \<equiv> (\<lambda> (bi, idx) . 
	idx \<le> l \<and>
	length bi = idx \<and>
	big_int_\<alpha> bi + big_int_\<alpha> (take idx ai) = limb_sz ^ idx - 1
)"

definition "compl_cond ai l \<equiv> (\<lambda> (bi, idx). idx < l)"

definition "big_int_compl ai l \<equiv> do {
	(bi, idx) \<leftarrow> WHILEIT (compl_invar ai l) (compl_cond ai l) (\<lambda> (bi, idx). do {
    let aidx = (get_or_zero ai idx);
    let aidx_compl = compl aidx;

    bi_next \<leftarrow> bi_append bi aidx_compl;
    ASSERT (idx+1 \<le> length bi_next);

    let idx = idx + 1;

		RETURN (bi_next, idx)
	}) (big_int0, 0);
  bi \<leftarrow> big_int_trim bi;
	RETURN bi
}"

lemma compl_correct': "(ai, a) \<in> big_int_rel \<Longrightarrow> l \<ge> length ai \<Longrightarrow> big_int_compl ai l \<le> SPEC (\<lambda> bi. (bi, limb_sz ^ l - a - 1) \<in> big_int_rel)"
	unfolding big_int_compl_def big_int0_def
	apply (refine_vcg bi_append_correct) 
	apply (rule wf_measure[where f="\<lambda>(bi, idx). l - idx"])

  (* Invar init *)
	subgoal unfolding compl_invar_def by auto

  (* Idx in usize *)
  subgoal using sepref_sorry by simp

  apply clarsimp
  (* Invar pres *)
	subgoal for bi idx unfolding compl_invar_def compl_cond_def
		apply (simp add: big_int_to_nat_append big_int_to_nat_Suc)
		subgoal proof -
			define lhs where "lhs = big_int_\<alpha> bi + limb_nat (compl( get_or_zero ai idx)) * limb_sz ^ idx + (big_int_\<alpha> (take idx ai) + limb_nat (get_or_zero ai idx) * limb_sz ^ idx)"
			assume "length bi = idx \<and> big_int_\<alpha> bi + big_int_\<alpha> (take idx ai) = limb_sz ^ idx - Suc 0"
			hence "lhs = 
				limb_sz ^ idx - Suc 0 + limb_nat (compl( get_or_zero ai idx)) * limb_sz ^ idx  + limb_nat (get_or_zero ai idx) * limb_sz ^ idx"
				using lhs_def by auto
			hence "lhs = limb_sz ^ idx - Suc 0 + (limb_nat (compl( get_or_zero ai idx)) + limb_nat (get_or_zero ai idx)) * limb_sz ^ idx"
				by (simp add: distrib_left mult.commute)
			hence "lhs = limb_sz ^ idx - Suc 0 + (limb_sz - 1) * limb_sz ^ idx"
				using compl_correct(2) limb_mx_suc
				by (simp add: add.commute limb_mx_def)
      hence "lhs = limb_sz ^ idx - Suc 0 + limb_sz * limb_sz ^ idx - limb_sz ^ idx"
        by (simp add: limb_mx_suc(2))
      hence "lhs = limb_sz * limb_sz ^ idx + limb_sz ^ idx - Suc 0 - limb_sz ^ idx"
        using limb_sz_gt(1) by force
			hence "lhs = limb_sz * limb_sz ^ idx - Suc 0"
        by simp
			thus ?thesis using lhs_def by simp
			qed
		done
	 apply clarsimp

  (* Measure decr *)
	subgoal unfolding compl_invar_def compl_cond_def by simp
	apply clarsimp

  (* Result post *)
	subgoal for bi idx
		apply (refine_vcg big_int_trim_correct)
		unfolding compl_invar_def compl_cond_def big_int_to_nat_lt big_int_trim_correct big_int_rel_def br_def
		by auto
	done

lemma big_int_rel_length_cmp:
	assumes "(ai, a) \<in> big_int_rel" "(bi, b) \<in> big_int_rel " "a \<le> b"
	shows "length ai \<le> length bi"
proof (cases "a")
	case 0
	hence "ai = big_int0" using big_int0_def big_int_zero_refine assms big_int_rel_unique by auto
	then show ?thesis using big_int0_def by auto
next
	case (Suc a')
	hence "a \<noteq> 0" by auto
	hence "a \<ge> limb_sz ^ (length ai - 1)" using big_int_rel_bounds assms by auto
	hence "b \<ge> limb_sz ^ (length ai - 1)" using assms by auto
	hence "limb_sz ^ length bi > limb_sz ^ (length ai - 1)" using big_int_rel_bounds assms order_le_less_trans by blast
	hence "length bi > length ai - 1" using limb_sz_gt by auto
	then show ?thesis by auto
qed


(* NOTE: this assumes ai \<ge> bi, otherwise returns limb_sz^l - a + b *)
definition "big_int_sub_compl ai bi \<equiv> do {
	let l = max (big_int_length ai) (big_int_length bi);
	nbi \<leftarrow> big_int_compl bi l;
	sum \<leftarrow> big_int_add_inc ai nbi;
  sum \<leftarrow> big_int_take l sum;
	RETURN sum
}"

lemma in_rel_abs_eqI: "(x,a)\<in>R \<Longrightarrow> a=b \<Longrightarrow> (x,b)\<in>R" by blast 

lemma big_int_sub_compl_correct: 
	"a \<ge> b \<Longrightarrow> (ai, a) \<in> big_int_rel \<Longrightarrow> (bi, b) \<in> big_int_rel \<Longrightarrow> big_int_sub_compl ai bi \<le> \<Down> big_int_rel (RETURN (a - b))"
	unfolding big_int_sub_compl_def
	apply (refine_vcg big_int_add_inc_correct' compl_correct' big_int_trim_correct big_int_one_refine big_int_take_correct')
	apply (all \<open>assumption?\<close>) 
	subgoal using big_int_rel_length_cmp[of bi b ai a] big_int_length_def by force
  subgoal for bi_comp ai_bi ai_bi_mod proof -
    assume arel: "(ai, a) \<in> big_int_rel"
    assume brel: "(bi, b) \<in> big_int_rel"
    assume a_le_b: "b \<le> a"

    assume 0: "(ai_bi_mod,
     (a + (limb_sz ^ max (big_int_length ai) (big_int_length bi) - b - 1) + 1) mod limb_sz ^ max (big_int_length ai) (big_int_length bi))
    \<in> big_int_rel"
    define limb_pow where "limb_pow = limb_sz ^ max (big_int_length ai) (big_int_length bi)"

    hence 1: "(ai_bi_mod, (a + (limb_pow - b - 1) + 1) mod limb_pow)\<in> big_int_rel"
      using 0 by auto

    have "limb_pow \<ge> limb_sz ^ (big_int_length ai)"      
      using limb_sz_gt(1) limb_pow_def by auto
    hence a_lt: "limb_pow > a"
      using arel big_int_length_pow_gt dual_order.strict_trans1 by blast

    have  "limb_pow \<ge> limb_sz ^ (big_int_length bi)"
      using limb_sz_gt(1) limb_pow_def by auto
    hence b_lt: "limb_pow > b"
      using brel big_int_length_pow_gt dual_order.strict_trans1 by blast

    have "a + (limb_pow - b - 1) + 1 = limb_pow + a - b"
      using a_lt b_lt by force

    hence 2: "(ai_bi_mod, (limb_pow + a - b) mod limb_pow) \<in> big_int_rel"
      using 1 by presburger

    thus ?thesis using a_le_b a_lt b_lt
      by (metis mod_add_self1 mod_nat_sub ordered_cancel_comm_monoid_diff_class.diff_add_assoc)
  qed
  done



lemma big_int_sub_compl_correct': 
	"a \<ge> b \<Longrightarrow> (ai, a) \<in> big_int_rel \<Longrightarrow> (bi, b) \<in> big_int_rel \<Longrightarrow> big_int_sub_compl ai bi \<le> (SPEC (\<lambda> c. (c, (a - b)) \<in> big_int_rel))"
	unfolding big_int_sub_compl_def
  using big_int_sub_compl_correct
  by (simp add: big_int_sub_compl_def conc_fun_RETURN)

definition big_int_sub_cond :: "big_int \<Rightarrow> big_int \<Rightarrow> (big_int \<times> nat \<times> limb) \<Rightarrow> bool" where "big_int_sub_cond ai bi \<equiv> ( \<lambda>(ci, idx, cr).
    idx \<le> max (big_int_length ai) (big_int_length bi))"

definition big_int_sub_invar :: "big_int \<Rightarrow> big_int \<Rightarrow> (big_int \<times> nat \<times> limb) \<Rightarrow> bool" where "big_int_sub_invar ai bi \<equiv> ( \<lambda>(ci, idx, cr).
    big_int_\<alpha> (take idx ai) + (limb_nat cr) * limb_sz ^ idx = big_int_\<alpha> (take idx bi) + big_int_\<alpha> ci
    \<and> cr \<in> {0, 1}
    \<and> idx = big_int_length ci)"

definition big_int_sub_body :: "big_int \<Rightarrow> big_int \<Rightarrow> (big_int \<times> nat \<times> limb) \<Rightarrow> (big_int \<times> nat \<times> limb) nres" where
  "big_int_sub_body ai bi \<equiv> (\<lambda>(ci, idx, cr). do {
    let aix = get_or_zero ai idx;
    let bix = get_or_zero bi idx;
    let (cix, new_cr) = sub_carry aix bix cr;

    ci \<leftarrow> bi_append ci cix;
    ASSERT (idx+1 \<le> length ci);

    let idx = idx + 1;

    RETURN (ci, idx, new_cr)
  })"


definition big_int_sub :: "big_int \<Rightarrow> big_int \<Rightarrow> (big_int \<times> bool) nres" where "big_int_sub ai bi \<equiv> do {
  (ci, idx, cr) \<leftarrow> WHILEIT 
    (big_int_sub_invar ai bi)
    (big_int_sub_cond  ai bi)
    (big_int_sub_body  ai bi)
    (big_int0, 0, 0);

  ci \<leftarrow> big_int_trim ci;

  RETURN (ci, cr > 0)
}"

find_consts "('a \<Rightarrow> 'b nres) \<Rightarrow> ('a nres) \<Rightarrow> ('b nres)"
find_theorems "big_int_\<alpha>" "take"


lemma big_int_rel_length_rev: "(ai, a) \<in> big_int_rel \<Longrightarrow> size_log a = length ai"
  using big_int_rel_length_log by simp

lemma big_int_\<alpha>_unwrap: "(ai, a) \<in> big_int_rel \<Longrightarrow> big_int_\<alpha> ai = a"
  by (simp add: big_int_rel_def in_br_conv)

lemma big_int_sub_correct_aux: "(ai, a) \<in> big_int_rel \<Longrightarrow> (bi, b) \<in> big_int_rel \<Longrightarrow> 
  big_int_sub ai bi \<le> SPEC (\<lambda>(ci, cr). if cr 
  then a < b 
  else a = b + big_int_\<alpha> ci \<and> big_int_invar ci)"
	unfolding big_int_sub_def big_int_sub_body_def big_int_sub_cond_def bi_append_def
  apply (refine_vcg big_int_trim_correct)
  apply (rule wf_measure[where f="\<lambda>(ci, idx, cr). (max (length ai) (length bi) + 2 - idx)"])
  subgoal using big_int_sub_invar_def big_int_length_correct by auto

  subgoal by simp

  unfolding big_int_sub_cond_def big_int_sub_invar_def big_int_length_def
  
  subgoal by simp
    apply clarsimp

  subgoal for ci cr cidx new_cr proof -
    have idx_suc: "Suc (length ci) = length (ci @ [cidx])" unfolding big_int_length_def by auto

    assume cr: "cr = 0 \<or> cr = 1"

    define aidx where "aidx = get_or_zero ai (length ci)"
    define bidx where "bidx = get_or_zero bi (length ci)"

    assume "sub_carry (get_or_zero ai (length ci)) (get_or_zero bi (length ci)) cr = (cidx, new_cr)"
    hence sub_carry: "(cidx, new_cr) = sub_carry aidx bidx cr" using aidx_def bidx_def by simp
    hence sub: "limb_nat aidx + limb_sz * limb_nat new_cr = limb_nat bidx + limb_nat cidx + limb_nat cr"
      using sub_carry_correct cr by force
    hence sub_pow: "limb_nat aidx * (limb_sz ^ length ci) + limb_nat new_cr * (limb_sz * limb_sz ^ length ci) = 
      limb_nat bidx * (limb_sz ^ length ci) + limb_nat cidx * (limb_sz ^ length ci) + limb_nat cr * (limb_sz ^ length ci)"
      by (metis (no_types, lifting) add_mult_distrib mult.assoc mult.commute)

    have new_cr: "new_cr = 0 \<or> new_cr = 1" using sub_carry by (smt (verit) prod.inject sub_carry_def)

    have aidx: "big_int_\<alpha> (take (Suc (length ci)) ai) = big_int_\<alpha> (take (length ci) ai) + limb_nat aidx * (limb_sz ^ length ci)"
      using aidx_def big_int_to_nat_Suc by blast

    have bidx: "big_int_\<alpha> (take (Suc (length ci)) bi) = big_int_\<alpha> (take (length ci) bi) + limb_nat bidx * (limb_sz ^ length ci)"
      using bidx_def big_int_to_nat_Suc by blast

    have cidx: "big_int_\<alpha> (ci @ [cidx]) = big_int_\<alpha> ci + limb_nat cidx * (limb_sz ^ length ci)"
      using big_int_to_nat_append by simp

    assume IH: "big_int_\<alpha> (take (length ci) ai) + limb_nat cr * limb_sz ^ length ci 
            = big_int_\<alpha> (take (length ci) bi) + big_int_\<alpha> ci"

    have "big_int_\<alpha> (take (Suc (length ci)) ai) + limb_nat new_cr * (limb_sz * limb_sz ^ length ci) = 
      big_int_\<alpha> (take (length ci) ai) + limb_nat aidx * (limb_sz ^ length ci) + limb_nat new_cr * (limb_sz * limb_sz ^ length ci)"
      using aidx by auto
    also have "... =  big_int_\<alpha> (take (length ci) ai) + limb_nat bidx * (limb_sz ^ length ci) + limb_nat cidx * (limb_sz ^ length ci) + limb_nat cr * (limb_sz ^ length ci)"
      using sub_pow by auto
    also have "... = big_int_\<alpha> (take (length ci) bi) + big_int_\<alpha> ci + limb_nat bidx * (limb_sz ^ length ci) + limb_nat cidx * (limb_sz ^ length ci)"
      using IH by auto
    also have "... = big_int_\<alpha> (take (Suc (length ci)) bi) + big_int_\<alpha> ci + limb_nat cidx * (limb_sz ^ length ci)"
      using bidx by auto
    also have "... = big_int_\<alpha> (take (Suc (length ci)) bi) + big_int_\<alpha> (ci @ [cidx])" 
      using cidx by auto

    finally
    show ?thesis using new_cr by auto
  qed
  subgoal by auto
  apply (clarsimp simp: big_int_\<alpha>_unwrap)

  subgoal for ci cr res 
    apply (cases "0 < cr")
    apply clarsimp
    subgoal proof -
      have LT: "big_int_\<alpha> ci < limb_sz ^ length ci"
        using big_int_to_nat_lt by presburger

      assume invar: "a + limb_nat cr * limb_sz ^ length ci = b + big_int_\<alpha> ci"
      assume "0 < cr" and "cr = 0 \<or> cr = 1" 
      hence "cr = 1" by auto
      hence "limb_nat cr = 1" by simp
      hence "a + limb_sz ^ length ci = b + big_int_\<alpha> ci" using invar by auto
      thus ?thesis using LT invar by auto
    qed
    by auto
  done


lemma big_int_sub_correct:
  "(ai, a) \<in> big_int_rel \<Longrightarrow> (bi, b) \<in> big_int_rel \<Longrightarrow> (big_int_sub ai bi) \<le> SPEC 
    (\<lambda>(ci, cr). if a < b then cr else (ci, a - b) \<in> big_int_rel)"
  apply (cases "a < b")
  apply simp
  apply (rule order.trans[OF big_int_sub_correct_aux])
  apply assumption
  apply assumption
  subgoal by auto
  apply clarsimp
  subgoal proof -
    assume "\<not> a < b"
    hence cond: "a < b = False" by meson
    assume "(ai, a) \<in> big_int_rel" and "(bi, b) \<in> big_int_rel"
    hence "big_int_sub ai bi \<le> SPEC (\<lambda>(ci, cr). if cr 
      then a < b 
      else a = b + big_int_\<alpha> ci \<and> big_int_invar ci )" using big_int_sub_correct_aux by simp
    hence "big_int_sub ai bi \<le> SPEC (\<lambda>(ci, cr). if cr then False
      else a = b + big_int_\<alpha> ci \<and> big_int_invar ci )" using cond SPEC_cons_rule by fastforce
    hence "big_int_sub ai bi \<le> SPEC (\<lambda>(ci, cr). a = b + big_int_\<alpha> ci \<and> big_int_invar ci )" 
      using SPEC_cons_rule by fastforce
    hence p: "big_int_sub ai bi \<le> SPEC (\<lambda>(ci, cr). a - b = big_int_\<alpha> ci \<and> big_int_invar ci)" using cond SPEC_cons_rule 
      by force
    thus ?thesis unfolding big_int_rel_def in_br_conv by meson
  qed
  done
  

(* Big Int Single Limb Mult. *)
definition big_int_fits_limb :: "big_int \<Rightarrow> bool" where
	"big_int_fits_limb ai \<equiv> length ai \<le> 1"

lemma big_int_\<alpha>_less_length: "big_int_invar ai \<Longrightarrow> big_int_\<alpha> ai < limb_sz ^ n \<Longrightarrow> length ai \<le> n"
	using big_int_rel_bounds  
	by (metis big_int_rel_def big_int_rel_length_log bot_nat_0.extremum floorlog_le_iff in_br_conv unat_lt2p unsigned_1 size_log_def limb_sz_unfold)

lemma big_int_fits_limb_correct[simp]: "big_int_invar ai \<Longrightarrow> big_int_fits_limb ai \<longleftrightarrow> big_int_\<alpha> ai < limb_sz"  
	using big_int_rel_bounds big_int_\<alpha>_less_length
	unfolding big_int_fits_limb_def big_int_rel_def in_br_conv
  by (metis limb_sz_gt(1) order.strict_trans2 power_increasing_iff power_one_right)
	
definition big_int_small_to_limb :: "big_int \<Rightarrow> limb nres" 
  where "big_int_small_to_limb ai \<equiv> do {
    ASSERT (length ai = 1);
    ASSERT (ai \<noteq> []);
    let aih = op_list_hd ai; 
    RETURN aih
  }"

find_theorems "big_int_length"

lemma big_int_small_to_limb_correct[simp]: 
	"(ai, a) \<in> big_int_rel \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> a < limb_sz \<Longrightarrow> big_int_small_to_limb ai \<le> SPEC (\<lambda> r. limb_nat r = a)"
	unfolding big_int_small_to_limb_def 
  apply refine_vcg
  thm "big_int_rel_bounds"
  subgoal proof - 
    assume lt: "a < limb_sz"
    assume  anz: "(ai, a) \<in> big_int_rel" "a \<noteq> 0"

    hence "limb_sz ^ (length ai - 1) \<le> a" using big_int_rel_bounds by blast
    hence "limb_sz ^ (length ai - 1) < limb_sz" using lt by linarith
    hence "length ai - 1 < 1"
      by (metis limb_sz_gt(1) power_one_right power_strict_increasing_iff)
    hence "length ai \<le> 1" by force
    thus ?thesis using anz
      by (metis big_int_length_def big_int_rel_length_log le_antisym less_le_not_le nat_geq_1_eq_neqz power_0 size_log_pow_lt)
  qed
  subgoal using big_int_length_def by force
	proof -
		assume rel: "(ai, a) \<in> big_int_rel"
    hence alpha: "big_int_\<alpha> ai = a" using big_int_rel_def in_br_conv
      by metis
		assume less: "a < limb_sz"
		assume len: "length ai = 1"
		then obtain x where "ai = [x]"
      unfolding big_int_length_def
			using list_decomp_1 by blast
		hence "a = limb_nat x" using alpha by simp 
		thus "limb_nat (op_list_hd ai) = a" using big_int_small_to_limb_def
			using \<open>ai = [x]\<close> by force
	qed
	


definition "big_int_mult_limb_invar ai c \<equiv> (\<lambda>(bi, idx, cr) . 
	length bi = idx \<and>
	idx \<le> length ai+1 \<and>
	(big_int_\<alpha> (take idx ai)) * limb_nat c = big_int_\<alpha> bi + limb_nat cr * limb_sz ^ idx
)"

definition big_int_mult_limb_aux :: "big_int \<Rightarrow> limb \<Rightarrow> big_int nres"
	where "big_int_mult_limb_aux ai c \<equiv> do {
	(bi, idx, cr) \<leftarrow> WHILEIT 
	(big_int_mult_limb_invar ai c) 
	(\<lambda> (bi, idx, cr) . idx < length ai \<or> cr \<noteq> 0) 
	(\<lambda> (bi, idx, cr) . do {
			let aidx = get_or_zero ai idx;
			let (rs, cr) = mul_add aidx c cr;

      bi_next \<leftarrow> bi_append bi rs;
      ASSERT (idx+1 \<le> length bi_next);

			RETURN (bi_next, idx + 1, cr)
		}
	) (big_int0, 0, 0);
	RETURN bi
	}"

lemma helper: "n < limb_sz ^ 2 \<Longrightarrow> n = limb_nat ((word_of_nat (n mod limb_sz))) + limb_nat ((word_of_nat (n div limb_sz))) * limb_sz"
	by (simp add: Word.unat_of_nat limb_sz_unfold limb_nat_def)

lemma big_int_limb_aux_correct: "(ai, a) \<in> big_int_rel \<Longrightarrow> c = limb_nat ci \<Longrightarrow> big_int_mult_limb_aux ai ci \<le> SPEC (\<lambda> r. big_int_to_nat r = a * c)"
	unfolding big_int_rel_def br_def big_int_mult_limb_aux_def bi_append_def big_int0_def
	apply refine_vcg
	apply (rule wf_measure[where f="\<lambda>(bi, idx, cr) . length ai + 2 - idx"])
	subgoal unfolding big_int_mult_limb_invar_def by simp

	(* Length assumption *)
  subgoal by simp

  subgoal unfolding big_int_mult_limb_invar_def by simp

  apply clarsimp

	subgoal for bi idx cr bidx next_cr
		apply (unfold big_int_mult_limb_invar_def)
		apply (clarsimp simp: Let_def)
		apply (intro conjI)
		subgoal
			proof (cases "length bi \<le> length ai")
			  case True
			  then show ?thesis by auto
			next
			  case False
			  assume iv: "big_int_\<alpha> (take (length bi) ai) * limb_nat ci = big_int_\<alpha> bi + limb_nat cr * limb_sz ^ length bi"
			  assume "length bi < length ai \<or> cr \<noteq> 0" 
        hence "cr \<noteq> 0" using False by auto
			  hence 1: "limb_nat cr * limb_sz ^ length bi \<ge> limb_sz ^ length bi" by (simp add: limb_nat_def le_def unat_gt_0)


        note False
			  hence "take (length bi) ai = ai" using take_all by simp
			  hence "big_int_\<alpha> (take (length bi) ai) = big_int_\<alpha> ai" by auto
			  hence 2: "big_int_\<alpha> bi + limb_nat cr * limb_sz ^ length bi = big_int_\<alpha> ai * limb_nat ci" using iv limb_nat_def
			    by argo

			  have "big_int_\<alpha> ai < limb_sz ^ length ai" using big_int_to_nat_lt by auto
			  hence "big_int_\<alpha> ai * limb_nat ci < limb_sz ^ length ai * limb_sz" using  mult_strict_mono' limb_nat_lt by blast
			  hence "big_int_\<alpha> ai * limb_nat ci < limb_sz ^ (Suc (length ai))" by (simp add: mult.commute)
			  hence "limb_sz ^ (Suc (length ai)) > limb_sz ^ length bi" using 1 2 
			    by (metis order_le_less_trans trans_le_add2)
			  hence "Suc (length ai) > length bi" using limb_sz_gt power_less_imp_less_exp by blast
			  then show ?thesis using False by auto
			qed
		subgoal 
			apply (unfold big_int_to_nat_append big_int_to_nat_Suc Let_def)
			apply (rule trans[OF distrib_right])
      apply (clarsimp)
			subgoal proof - 
        assume fma: "mul_add (get_or_zero ai (length bi)) ci cr = (bidx, next_cr)"

				define res where "res = limb_nat (get_or_zero ai (length bi)) * limb_nat ci + limb_nat cr"
				hence res_lt: "res < limb_sz ^ 2" using limb_nat_le mul_add_fits by auto
				hence 1: "res = limb_nat ((word_of_nat (res mod limb_sz))) + limb_nat ((word_of_nat (res div limb_sz))) * limb_sz"
					using helper[of "res"]
					by fastforce

        have bidx:"limb_nat bidx = res mod limb_sz" using mul_add_correct fma
          by (metis fst_conv res_def)

        have next_cr: "limb_nat next_cr = res div limb_sz" using mul_add_correct fma
          by (metis snd_conv res_def)

				define lhs where "lhs = limb_nat cr * limb_sz ^ length bi + limb_nat (get_or_zero ai (length bi)) * limb_sz ^ length bi * limb_nat ci"
				hence "lhs = 
						(limb_nat cr + limb_nat (get_or_zero ai (length bi)) * limb_nat ci) * limb_sz ^ length bi " using add_mult_distrib by force
				hence "lhs = res * limb_sz ^ length bi" using res_def by auto
				hence "lhs = (limb_nat ((nat_limb (res mod limb_sz))) + limb_nat (nat_limb (res div limb_sz)) * limb_sz) * limb_sz ^ length bi"
					using 1 nat_limb_def by argo
				hence "lhs = (limb_nat (nat_limb (res mod limb_sz)) * limb_sz ^ length bi) + (limb_nat (nat_limb (res div limb_sz))) * (limb_sz * limb_sz ^ length bi)"
					by (simp add: add_mult_distrib)

				then show ?thesis using lhs_def res_def 1
				  by (metis bidx limb_nat_id(2) next_cr)
				qed
			done
		done
	apply clarsimp
	subgoal for bi idx cr bidx next_cr
		unfolding big_int_mult_limb_invar_def by auto
	apply clarsimp
	subgoal for bi idx
		unfolding big_int_mult_limb_invar_def 
		apply simp
		done
	done

definition big_int_mult_limb :: "big_int \<Rightarrow> limb \<Rightarrow> big_int nres"
	where "big_int_mult_limb ai c \<equiv> do {
		bi \<leftarrow> big_int_mult_limb_aux ai c;
		bi \<leftarrow> big_int_trim bi;
    RETURN bi
	}"

lemma big_int_mult_limb_correct: 
	assumes "(ai, a) \<in> big_int_rel" "c = limb_nat ci" 
	shows "big_int_mult_limb ai ci \<le> \<Down> big_int_rel (RETURN (a * c))" 
	using assms unfolding big_int_mult_limb_def
	apply (refine_vcg big_int_limb_aux_correct assms big_int_trim_correct)
	unfolding big_int_rel_def by (auto simp: in_br_conv)

lemma big_int_mult_limb_correct':
	assumes "(ai, a) \<in> big_int_rel" "c = limb_nat ci" 
	shows "big_int_mult_limb ai ci \<le> SPEC (\<lambda> ci. (ci, (a * c)) \<in> big_int_rel)"
	using assms unfolding big_int_mult_limb_def
	apply (refine_vcg big_int_limb_aux_correct assms big_int_trim_correct)
	unfolding big_int_rel_def by (auto simp: in_br_conv)

definition big_int_mult_school_invar :: "big_int \<Rightarrow> big_int \<Rightarrow> (big_int \<times> nat) \<Rightarrow> bool"
  where "big_int_mult_school_invar ai bi \<equiv> (\<lambda>(ci, idx). 
    big_int_to_nat (take idx ai) * big_int_to_nat bi = big_int_to_nat ci \<and>
    big_int_invar ci \<and>
    idx \<le> length ai)"

definition big_int_mult_school_cond :: "big_int \<Rightarrow> big_int \<Rightarrow> (big_int \<times> nat) \<Rightarrow> bool"
  where "big_int_mult_school_cond ai bi \<equiv> (\<lambda>(ci, idx). idx < length ai)"

definition big_int_mult_school_body :: "big_int \<Rightarrow> big_int \<Rightarrow> (big_int \<times> nat) \<Rightarrow> (big_int \<times> nat) nres"
  where "big_int_mult_school_body ai bi \<equiv> (\<lambda>(ci, idx). do {
    let aidx = get_or_zero ai idx;
    if aidx = 0 then 
      RETURN (ci, idx + 1)
    else do {
      aidx_bi_prod \<leftarrow> big_int_mult_limb bi aidx;
      ai_bi_prod \<leftarrow> big_int_rshift idx aidx_bi_prod;
      ci \<leftarrow> big_int_add ci ai_bi_prod;
      RETURN (ci, idx + 1)
    }
})"


definition big_int_mult_school :: "big_int \<Rightarrow> big_int \<Rightarrow> big_int nres"
  where "big_int_mult_school ai bi \<equiv> do {
    (ci, idx) \<leftarrow> WHILEIT 
      (big_int_mult_school_invar ai bi)
      (big_int_mult_school_cond ai bi)
      (big_int_mult_school_body ai bi)
      (big_int0, 0);
    RETURN ci
  }"

lemma big_int_mult_school_correct: 
  "(ai, a) \<in> big_int_rel \<Longrightarrow> (bi, b) \<in> big_int_rel \<Longrightarrow> big_int_mult_school ai bi \<le> \<Down> big_int_rel
      (RETURN (a * b))"
  unfolding big_int_mult_school_def 
    big_int_mult_school_invar_def big_int_mult_school_cond_def
    big_int_mult_school_body_def 
  apply (refine_vcg big_int_mult_limb_correct' big_int_add_correct')
  apply (rule wf_measure[where f="\<lambda>(ci, idx). length ai - idx"])
  unfolding big_int_rel_def in_br_conv 
  apply (all \<open>((simp; assumption)+)?\<close>)
  subgoal using big_int_to_nat_Suc by auto
  apply clarsimp
  subgoal for ci idx aidx_bi ai_bi ci_next proof -

    assume ci: "big_int_\<alpha> (take idx ai) * big_int_\<alpha> bi = big_int_\<alpha> ci"
    assume ai_bi: "big_int_\<alpha> aidx_bi * limb_sz ^ idx = big_int_\<alpha> ai_bi"
    assume aidx_bi: "big_int_\<alpha> bi * limb_nat (get_or_zero ai idx) = big_int_\<alpha> aidx_bi"

    assume "big_int_\<alpha> ci + big_int_\<alpha> ai_bi = big_int_\<alpha> ci_next"
    hence "... = big_int_\<alpha> ci + big_int_\<alpha> ai_bi" by simp 
    also have "... = big_int_\<alpha> (take idx ai) * big_int_\<alpha> bi + big_int_\<alpha> aidx_bi * limb_sz ^ idx"
      using ci ai_bi by simp
    also have "... = big_int_\<alpha> (take idx ai) * big_int_\<alpha> bi + big_int_\<alpha> bi * limb_nat (get_or_zero ai idx) * limb_sz ^ idx"
      using aidx_bi by simp
    also have "... = (big_int_\<alpha> (take idx ai) + limb_nat (get_or_zero ai idx) * limb_sz ^ idx) * big_int_\<alpha> bi"
      by algebra
    also have "... = (big_int_\<alpha> (take (Suc idx) ai)) * big_int_\<alpha> bi"
      using big_int_to_nat_Suc by auto
    finally show ?thesis by simp
  qed
  subgoal by simp
  done


end