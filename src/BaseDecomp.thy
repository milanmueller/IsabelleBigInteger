theory BaseDecomp
  imports Main Setup
 "HOL-Computational_Algebra.Polynomial"
begin

(* Helper lemmas *)
lemma horner_sum_id_map: "horner_sum id x (map f ls) = horner_sum f x ls"
  apply (induction ls)
  by simp+


locale base_decomp =
  fixes base :: "nat"
  assumes base_gt: "base \<ge> 2"
begin

  lemma base_nz[simp]: "\<not> (base = 0)" using base_gt by simp 

  lemma decomp_order[termination_simp]: "n > 0 \<Longrightarrow> n div base < n"
    using base_gt by simp

  lemma mod_base_lt[simp]: "n mod base < base" using base_gt by simp

  lemma base_pow_mono[simp]: "a < b \<Longrightarrow> base ^ a < base ^ b" using base_gt by simp 

  (* Convention 0 has 0 digits *)
  fun digits :: "nat \<Rightarrow> nat" where
    "digits 0 = 0" 
  | "digits n = 1 + digits (n div base)"
  
  lemma [code]: "digits n = (if n = 0 then 0 else 1 + digits (n div base))"
    by (metis digits.simps(1) digits.elims)
  
  lemma digits_mono: "x \<le> y \<Longrightarrow> digits x \<le> digits y"
    apply (induction y arbitrary: x rule: digits.induct)  
    subgoal by force
    subgoal for y' x proof -
      assume IH: "\<And>x. x \<le> Suc y' div base \<Longrightarrow> digits x \<le> digits (Suc y' div base)"
      assume leq: "x \<le> Suc y'"
      hence "x div base \<le> Suc y' div base" using base_gt using div_le_mono by presburger
      hence "digits (x div base) \<le> digits (Suc y' div base)" using IH by presburger
      thus ?thesis by (cases x; auto)
    qed
    done
  
  lemma base_pow_lt_digits: "x < base ^ n \<longleftrightarrow> digits x \<le> n"
    apply rule
    subgoal 
      apply (induction x arbitrary: n rule:digits.induct)
       apply fastforce
      subgoal for m n proof -
        assume IH: "\<And>n. Suc m div base < base ^ n \<Longrightarrow> digits (Suc m div base) \<le> n"
        have digits: "digits (Suc m) = 1 + digits (Suc m div base)" by fastforce
  
        assume bound: "Suc m < base ^ n"
        hence "n > 0" by (cases n; auto)
        then obtain n' where n': "Suc n' = n" 
          using gr0_implies_Suc by auto 
        hence "Suc m div base < base ^ n'" 
          by (metis bound n' less_mult_imp_div_less power_Suc mult.commute)
        hence "digits (Suc m div base) \<le> n'" using IH[of n'] by blast
        hence "digits (Suc m) \<le> 1 + n'" using digits by simp
        thus "digits (Suc m) \<le> n" using n' by fastforce
      qed
      done
    subgoal  
      apply (induction x arbitrary: n rule: digits.induct)
      using base_gt apply force
      subgoal for m n proof -
        assume IH: "\<And>n. digits (Suc m div base) \<le> n \<Longrightarrow> Suc m div base < base ^ n"
        have digits: "digits (Suc m) = 1 + digits (Suc m div base)" by fastforce
  
        assume bound: "digits (Suc m) \<le> n"
        hence cmp: "1 + digits (Suc m div base) \<le> n" using digits by argo
        hence "n > 0" by force
        then obtain n' where n': "Suc n' = n"
          using gr0_implies_Suc by auto
        hence "digits (Suc m div base) \<le> n'" using cmp by fastforce
        hence "Suc m div base < base ^ n'" using IH[of n'] by presburger
        hence "Suc m < base ^ n' * base" using base_gt div_less_iff_less_mult by auto
        hence "Suc m < base ^ (Suc n')" by (simp add: mult.commute)
        thus "Suc m < base ^ n" using n' by argo
      qed
      done
    done

  corollary base_pow_geq_digits: "x \<ge> base ^ n \<longleftrightarrow> digits x > n"
    using base_pow_lt_digits by (metis linorder_not_less)
  
  lemma base_pow_digits: "digits (base ^ n) = n + 1"
  proof (cases "digits (base ^ n) \<ge> n + 1")
    case True
    have "base ^ n < base ^ (Suc n)" using base_gt by auto
    hence "base ^ n < base ^ (Suc n) = True" by presburger
    hence "digits (base ^ n) \<le> Suc n = True" using base_pow_lt_digits[of "base ^ n" "Suc n"]
      by presburger
    hence leq: "digits (base ^ n) \<le> n + 1" by auto
    then show ?thesis using True by force
  next
    (* Contradiction proof *)
    case False
    hence "digits (base ^ n) \<le> n" by linarith
    hence "base ^ n < base ^ n" using base_pow_lt_digits[of "base ^ n" "n"] by presburger
    then show ?thesis by simp
  qed
  
  
  fun base_decomp :: "nat \<Rightarrow> nat list" where
    "base_decomp 0 = []"
  | "base_decomp n = (n mod base) # 
      base_decomp (n div base)"

  (* Note: recursive unfolding *)
  lemma base_decomp_step: "base_decomp n = (if n = 0 then [] else (n mod base) # base_decomp (n div base))"
    by (metis base_decomp.simps(1,2) list_decode.cases)

  lemma digits_length_decomp[simp]: "length (base_decomp n) = digits n"
    apply (induction rule: less_induct
        [where P="\<lambda>n. length (base_decomp n) = digits n"])
    subgoal for n
      apply (cases n)
      apply clarsimp
      subgoal for m 
        apply simp
        subgoal proof -
        assume IH: "(\<And>y. y < Suc m \<Longrightarrow> length (local.base_decomp y) = digits y)"
        define q where "q = Suc m div base"
        hence "q < Suc m" using decomp_order by blast
        hence "length (local.base_decomp q) = digits q" using IH by fastforce
        hence "length (local.base_decomp (Suc m div base)) = digits (Suc m div base)"
          unfolding q_def by presburger
        thus ?thesis .
      qed
      done
    done
  done

  fun base_decomp_inv :: "nat list \<Rightarrow> nat" where 
    "base_decomp_inv [] = 0"
  | "base_decomp_inv (x#xs) = x + base * base_decomp_inv xs"

  abbreviation "base_\<alpha> \<equiv> base_decomp_inv"

  lemma base_decomp_inv_not_zero : "xs \<noteq> [] \<Longrightarrow> last xs \<noteq> 0 \<Longrightarrow> base_\<alpha> xs \<noteq> 0" 
  apply (cases xs)
  apply simp
  subgoal for y ys
    apply (induction ys arbitrary: xs y)
    apply simp
    subgoal for z zs ys y proof -
      assume IH: "(\<And>xs y. xs \<noteq> [] \<Longrightarrow> last xs \<noteq> 0 \<Longrightarrow> xs = y # zs \<Longrightarrow> base_\<alpha> xs \<noteq> 0)"
      assume last: "last ys \<noteq> 0"  
      assume ys: "ys = y # z # zs"
      hence "last ys = last (y # z # zs)" by presburger
      also have "... = last (z # zs)" by simp
      finally have "... \<noteq> 0" using last by metis
      hence 1:"base_\<alpha> (z # zs) \<noteq> 0" using IH by blast
      have 2: "base_\<alpha> ys = y + base * base_\<alpha> (z # zs)" using ys by simp
      show ?thesis unfolding 2 using 1 base_gt by simp qed
    done
  done

  lemma base_decomp_inv_horner_sum: "base_decomp_inv ls = horner_sum (id) base ls"
    apply (induction ls)
    by simp+

  (* NOTE: we allow leading 0 digits on abstract level *)
  definition base_invar :: "nat list \<Rightarrow> bool" 
    where "base_invar \<equiv> (\<lambda> xs. (ALL x. x\<in> set xs \<longrightarrow> x < base))"

  lemma base_decomp_thus_invar: "base_invar (base_decomp n)"
    unfolding base_invar_def 
    apply (induction n rule: base_decomp.induct)
    by auto

  lemma base_invar_bound: "base_invar xs \<Longrightarrow> base_\<alpha> xs < base ^ length xs"
    apply (induction xs rule: base_decomp_inv.induct)
    subgoal by fastforce
    unfolding base_invar_def
    subgoal for x xs
      by (simp; metis add.commute mlex_bound mult.commute)
    done


  definition "base_rel \<equiv> br base_decomp_inv base_invar"

  lemma base_zeros: "base_\<alpha> (replicate n 0) = 0"
    by (induction n; auto)

  lemma base_rel_empty_inj[simp]: "([], a) \<in> base_rel \<Longrightarrow> a = 0" 
    unfolding base_rel_def in_br_conv by simp  

  lemma invar_tl_pres: "base_invar ai \<Longrightarrow> base_invar (tl ai)"
    unfolding base_invar_def 
    by (cases ai; auto)


  corollary invar_drop_pres: "base_invar ai \<Longrightarrow> base_invar (drop i ai)"
    unfolding base_invar_def
    by (metis in_set_dropD)

  corollary invar_take_pres: "base_invar ai \<Longrightarrow> base_invar (take i ai)"
    unfolding base_invar_def
    by (metis in_set_takeD)

  lemma base_cons: "base_\<alpha> (x#xs) = x + base * base_\<alpha> xs" 
    by simp

  corollary base_tail: "base_invar ai \<Longrightarrow> base_\<alpha> (tl ai) = base_\<alpha> ai div base"
    apply (cases ai)
    subgoal using base_rel_empty_inj by fastforce 
    subgoal for x xs unfolding base_invar_def by auto
    done

  corollary base_drop: "base_invar ai \<Longrightarrow> base_\<alpha> (drop k ai) = base_\<alpha> ai div base ^ k"
    apply (induction k arbitrary: ai)
    subgoal by simp
    using invar_tl_pres
    by (auto simp: drop_Suc base_tail div_mult2_eq)
    

  lemma base_append: "base_\<alpha> (xs @ ys) = base_\<alpha> xs + (base_\<alpha> ys) * base ^ (length xs)"
    apply (induction xs)
    by (auto simp: distrib_left mult.commute)

  lemma base_snoc: "base_\<alpha> (xs @ [x]) = base_\<alpha> xs + x * base ^ (length xs)"
    using base_append[of xs "[x]"] by simp

  lemma base_take: "base_invar xs \<Longrightarrow> base_\<alpha> (take i xs) = (base_\<alpha> xs) mod base ^ i" 
    apply(rewrite in "_ = \<hole>" append_take_drop_id[of i xs, symmetric] )
    unfolding base_append
    apply (cases "i \<le> length xs")
    apply auto
    subgoal using base_invar_bound[of "take i xs"] invar_take_pres by simp
    subgoal using base_invar_bound[of "xs"] base_pow_mono[of "length xs" "i"]
      by (simp add: base_pow_lt_digits)
    done

  subsection \<open>Polynomial representation\<close>
  (* TODO: decide if this is of any use *)

  (* This removes leading (trailing) 0's (i.e. what we call big_int_trim) *)
  abbreviation base_poly :: "nat list \<Rightarrow> nat poly"
    where "base_poly xs \<equiv> Poly xs"
  
  abbreviation poly_base :: "nat poly \<Rightarrow> nat list"
    where "poly_base p \<equiv> coeffs p"
  
  abbreviation poly_eval :: "nat poly \<Rightarrow> nat \<Rightarrow> nat"
    where "poly_eval p \<equiv> poly p"
  
  abbreviation poly_value :: "nat poly \<Rightarrow> nat"
    where "poly_value p \<equiv> poly_eval p base"

  abbreviation base_eval :: "nat list \<Rightarrow> nat \<Rightarrow> nat"
    where "base_eval xs \<equiv> poly_eval (base_poly xs)"
  
  abbreviation base_value :: "nat list \<Rightarrow> nat"
    where "base_value xs \<equiv> base_eval xs base"

  (* same as Big Int get_or_zero *)
  lemma "coeff (base_poly xs) i = nth_default 0 xs i" by fastforce

  (* Polynomial evaluation at \<open>x = base\<close> is equal to abstraction *)
  lemma value_decomp_inv: "base_value xs = base_\<alpha> xs" 
    apply (induction xs)
    subgoal by simp
    unfolding base_decomp_inv_horner_sum poly_def
    unfolding poly_def horner_sum_simps coeffs_Poly strip_while_def
    subgoal for x xs
      apply (cases " \<forall>x\<in>set (rev xs). ((=) 0) x")     
      apply (simp add: dropWhile_append)
      apply (metis (mono_tags, lifting) dropWhile_eq_Nil_conv horner_sum_simps(1) rev.simps(1) set_rev)
      apply (simp add: dropWhile_append)
      apply fast
      done
   done
    
  lemma value_decomp_eq: "base_value (base_decomp x) = x"
    apply (induction rule: base_decomp.induct)
    apply simp
    by (simp add: Poly_snoc poly_monom)

  corollary base_decomp_inv_abs: "base_\<alpha> (base_decomp x) = x"
    using value_decomp_eq value_decomp_inv by simp

  lemma "base_\<alpha> (base_decomp x) = y \<longleftrightarrow> x = y" using base_decomp_inv_abs by auto

  lemma base_decomp_bij: "base_decomp x = base_decomp y \<longleftrightarrow> x = y"
    by (metis value_decomp_eq)

  (* Note: since we allow leading 0's on this level, base representation is not unique *)
  lemma base_rel_unique: "(ai, a) \<in> base_rel \<Longrightarrow> (bi, b) \<in> base_rel \<Longrightarrow> (ai = bi)  \<longleftrightarrow> (a = b)" oops


  definition "base_strict_rel \<equiv> {(ai, a). base_decomp a = ai}"
  definition "base_strict_invar ai \<equiv> base_invar ai \<and> (ai = [] \<or> last ai \<noteq> 0)"

  lemma base_decomp_empty_iff: "base_decomp a = [] \<longleftrightarrow> a = 0" 
    by (metis base_decomp_inv_abs base_decomp.simps(1))

  lemma base_decomp_not_empty_last_nz: "base_decomp a \<noteq> [] \<Longrightarrow> last (base_decomp a) \<noteq> 0"
    apply (induction a rule: base_decomp.induct)
    apply (auto simp: base_decomp_empty_iff)
    by presburger

  find_theorems "base_invar" "base_decomp"

  lemma base_decomp_invar: "base_strict_invar (base_decomp a)"
    unfolding base_strict_invar_def
    using base_decomp_empty_iff base_decomp_not_empty_last_nz base_decomp_thus_invar by blast

  lemma base_invar_cons: "base_strict_invar ai \<Longrightarrow> ai = [] \<or> base_strict_invar (tl ai)"
    unfolding base_strict_invar_def base_invar_def
    by (metis in_set_tlD last_tl)

  lemma mod_div_unique: "a mod base = b mod base \<Longrightarrow> a div base = b div base \<Longrightarrow> a = b"
    by (metis div_mod_decomp) 

  lemma invar_then_unique: "base_strict_invar ai \<Longrightarrow> base_decomp (base_\<alpha> ai) = ai"
    apply (induction ai)
    subgoal by simp
    subgoal for a ai
      apply simp
      apply (frule base_invar_cons[of "a#ai"]; simp)
      apply (rewrite base_decomp_step)
      apply (cases "a + base * base_\<alpha> ai = 0")
      unfolding base_strict_invar_def base_invar_def
      by clarsimp+
    done

  lemma base_strict_subset: "(ai, a) \<in> base_strict_rel \<Longrightarrow> (ai, a) \<in> base_rel"
    unfolding base_rel_def base_strict_rel_def in_br_conv
    using base_decomp_inv_abs base_decomp_thus_invar by auto

  lemma base_strict_rel_unique: "(ai, a) \<in> base_strict_rel \<Longrightarrow> (bi, b) \<in> base_strict_rel \<Longrightarrow> 
   (ai = bi) \<longleftrightarrow> (a = b)" 
   apply (frule base_strict_subset)
   apply (frule base_strict_subset[of bi b])
   unfolding base_rel_def base_strict_rel_def in_br_conv 
   apply clarsimp
   by metis

  lemma base_strict_reversed: "base_\<alpha> ai = a \<Longrightarrow> base_strict_invar ai \<Longrightarrow> ai = base_decomp a"
    using invar_then_unique by auto

  lemma base_strict_rel_alt: "base_strict_rel = br base_\<alpha> base_strict_invar"
    unfolding base_strict_rel_def br_def
    apply auto
    subgoal using base_decomp_inv_abs by simp
    subgoal using base_decomp_invar by simp
    subgoal using base_strict_reversed by simp
    done


end (* END: base_decomp locale *)


(* Testing *)
global_interpretation base10: base_decomp 10
  defines decomp = "base_decomp.base_decomp 10"
      and digits = "base_decomp.digits 10"
  by unfold_locales (simp_all add: base_decomp_def)

value "decomp 100"



end