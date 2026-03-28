theory Division
  imports Main
  BaseDecomp "Isabelle_LLVM.IICF" Setup BigInt AuxLemmas Karatsuba BigIntSlice

begin

(* Notes:
  future work:  Using complex FFT \<rightarrow> float error bounding? 
*)
\<comment> \<open>\<^url>\<open>https://cp-algorithms.com/algebra/fft.html#number-theoretic-transform\<close>\<close>
(* \<^url>\<open>https://ridiculousfish.com/blog/posts/labor-of-division-episode-iv.html\<close> *)


definition div2by1 :: "limb \<Rightarrow> limb \<Rightarrow> limb \<Rightarrow> limb" where "div2by1 \<equiv> undefined"

definition basic_division :: "big_int \<Rightarrow> big_int \<Rightarrow> (big_int \<times> big_int) nres"
  where "basic_division ai bi \<equiv> doN {
    \<comment> \<open>TODO: Here we would normalize to increase msl of denominator bi\<close>
    let la = big_int_length ai;
    let lb = big_int_length bi;
    ASSERT (lb > 0); \<comment> \<open>Division by 0\<close>
    
    if la < lb then 
      RETURN (big_int0, ai \<comment>\<open>Possibly need to copy here\<close>)
    \<comment> \<open>TODO: Think about case la = lb\<close>
    else doN {
      (ai, bi) \<leftarrow> WHILEIT undefined (\<lambda>(ai, bi). big_int_length ai > big_int_length bi) (\<lambda>(ai, bi). doN {
        let la = big_int_length ai;
        let lb = big_int_length bi;
        ASSERT (la > lb);
        let len_diff = la - lb - 1;
        let a_high = big_int_last_limb ai;
        a_low  \<leftarrow> get_or_zero_fast ai (la - 2);

        let b_high = big_int_last_limb bi;

        \<comment> \<open>2by1 division (a_high * limb_sz + a_low / b_high)\<close>
        let q' = div2by1 a_high a_low b_high; \<comment> \<open>q' might be too high here\<close>
        

        \<comment> \<open>Question: do while break ?\<close>
        bi_shift \<leftarrow> big_int_rshift len_diff bi;
        q_bi \<leftarrow> big_int_mult_limb bi q';
        (ren, cr) \<leftarrow> big_int_sub ai q_bi;
        \<comment> \<open>If cr then we overshot\<close>
        \<comment> \<open>if cr then q' = q' - 1 else rem is the remaining portion of ai and q' is the digit of the result\<close>

        RETURN (ai, bi)
      }) (ai, bi);

      RETURN (big_int0, big_int0)
    }
  }"

  (* Manuel's Email: 
The rough idea is the following: we want to compute x / y for big
integers x and y, with each limb between 0 and b-1 (here b is some power
of two). First, as a pre-processing step, we make sure that the MSB in
the highest limb (bit?) of y is 1 by left-shifting x and y accordingly (Knuth
calls this "normalisation"). This does not change the quotient, but it
we will have to right-shift the remainder by the same amount in
post-processing. *)

lemma div_scale: "(k :: nat) > 0 \<Longrightarrow> a div b = (a * k) div (b * k)"
  by simp

lemma mod_scale: "(k :: nat) > 0 \<Longrightarrow> (a mod b) * k = (a * k) mod (b * k)"
  by simp



(* Shift 2 limbs to the left k bits *)
(* 2 [aaaa] [bbbb] \<rightarrow> aa [aabb] bb *)
definition limbs_bit_shift :: "nat \<Rightarrow> limb \<Rightarrow> limb \<Rightarrow> limb"
  where "limbs_bit_shift k a b \<equiv> (shiftl a k) || (shiftr b (limb_wd - k))"

(* NOTE: This could also be implemented using \<open>big_int_mult_limb\<close>, but that requires 128bit ops *)
term "big_int_mult_limb"

lemma bit_eq: "a = b \<longleftrightarrow> (ALL n. bit a n = bit b n)"
  by (metis bit_eq_iff)

lemma len_I: "\<not> 64 \<le> n \<longleftrightarrow> n < LENGTH(64)" by fastforce

lemma limbs_bit_shift_bit_list: "limbs_bit_shift k a b = of_bl ((drop k (to_bl a)) @ (take k (to_bl b)))"
  unfolding limbs_bit_shift_def bit_eq
  apply rule
  subgoal for n
  apply (cases "n \<ge> limb_wd")
  unfolding bit_of_bl_iff word_or_nth nth_shiftl nth_shiftr limb_wd_def
  apply clarsimp
  subgoal proof -
    assume CONTR: "b !! (n + (64 - k))"
    assume "64 \<le> n"
    hence "limb_wd \<le> n" using limb_wd_def by simp
    hence "limb_wd \<le> (n + (64 - k))" by simp
    hence "b !! (n + (64 - k)) = False" using test_bit_over by (simp add: limb_wd_def test_bit_bin)
    thus ?thesis using CONTR by blast
  qed
  apply (clarsimp simp: len_I)
  unfolding nth_append rev_take rev_drop 
  apply auto
  subgoal by (metis add.commute test_bit_bl)
  subgoal proof - 
    assume n_lt: "n < 64" 
    assume YES: "rev (to_bl b) ! (64 - k + n)"
    assume NO: "\<not> b !! (n + (64 - k))"
    assume cmp: "n < 64 - (64 - k)"

    hence 1: "64 - k + n < 64" by force
    hence "b !! (64 - k + n) = rev (to_bl b) ! (64 - k + n)" using nth_rev_to_bl[of "64 - k + n "] by force
    hence "b !! (n + (64 - k)) = ..." using 1 by (metis add.commute)
    hence "False" using YES NO by presburger
    thus ?thesis by satx
  qed
  (* SAME CONTR *)
  subgoal proof - 
    assume n_lt: "n < 64" 
    assume YES: "rev (to_bl b) ! (64 - k + n)"
    assume NO: "\<not> b !! (n + (64 - k))"
    assume cmp: "n < 64 - (64 - k)"

    hence 1: "64 - k + n < 64" by force
    hence "b !! (64 - k + n) = rev (to_bl b) ! (64 - k + n)" using nth_rev_to_bl[of "64 - k + n "] by force
    hence "b !! (n + (64 - k)) = ..." using 1 by (metis add.commute)
    hence "False" using YES NO by presburger
    thus ?thesis by satx
  qed
  subgoal by (metis test_bit_bl)
  unfolding not_less 
  (* TODO cleanup*)
  apply (metis (no_types, lifting) Nat.add_diff_assoc diff_is_0_eq' le_diff_conv len_I linorder_not_le nat_arith.rule0 nle_le test_bit_bin)
  by (meson len_I less_imp_diff_less linorder_not_le nth_rev_to_bl)
done

lemma length_limb_bit_list: "length (to_bl (a::limb)) = limb_wd"
  using limb_wd_def by auto

lemma limbs_bit_shift_bit_list': "k < limb_wd \<Longrightarrow> limbs_bit_shift k a b = of_bl (take limb_wd (drop k (to_bl a @ to_bl b)))"
  unfolding limbs_bit_shift_bit_list 
  using limb_wd_def by force

lemma "shiftl a n = of_bl ((drop n (to_bl a)) @ (replicate n False))"
  by (metis and_mask2 is_aligned_shift is_aligned_shiftr_shiftl of_drop_to_bl shiftl_of_bl)

lemma msb_shiftl_clz: "(a:: 'a::len word) \<noteq> 0 \<Longrightarrow> msb (shiftl a (word_clz a))" 
  by (auto simp add: word_msb_alt bl_shiftl word_clz_def eq_zero_set_bl in_set_conv_decomp_first[of _ "to_bl a"] takeWhile_append)

lemma limb_nat_add: "limb_nat (a + b) = (limb_nat a + limb_nat b) mod limb_sz"
  unfolding nat_limb_mod limb_add by simp

lemma limb_nat_mul: "limb_nat (a * b) = (limb_nat a * limb_nat b) mod limb_sz"
  unfolding nat_limb_mod limb_mul by simp

lemma k2pow_lt: "k < limb_wd \<Longrightarrow> 2 ^ k < limb_sz"
  unfolding limb_sz_def by auto

lemma k2pow_nat: "k < limb_wd \<Longrightarrow> limb_nat (2 ^ k) = 2 ^ k"
  using k2pow_lt
  by (metis mod_less nat_limb_def nat_limb_mod word_unat_power)

lemma k2pow_nat2: "0 < k \<Longrightarrow> k < limb_wd \<Longrightarrow> limb_nat (2 ^ (limb_wd - k)) = 2 ^ (limb_wd - k)"
  using k2pow_nat[of "limb_wd - k"] by fastforce
 
lemma limb_bit_shift_left: "k < limb_wd \<Longrightarrow> limb_nat (shiftl a k) = (limb_nat a * 2 ^ k) mod limb_sz"
  unfolding semiring_bit_operations_class.shiftl_eq_mult limb_nat_mul k2pow_nat
  by blast

lemma limb_nat_div: "limb_nat (a div b) = limb_nat a div limb_nat b" 
  by (metis unat_div limb_nat_def)

lemma limb_bit_shift_right: "0 < k \<Longrightarrow> k < limb_wd \<Longrightarrow> limb_nat (shiftr b (limb_wd - k)) = (limb_nat b) div 2 ^ (limb_wd - k)"
  unfolding semiring_bit_operations_class.shiftr_eq_div limb_nat_div k2pow_nat2 by simp

lemma k_decomp: "0 < k \<Longrightarrow> k < limb_wd \<Longrightarrow> limb_wd = k + (limb_wd - k)" by fastforce 

lemma k_pow_decomp: "0 < k \<Longrightarrow> k < limb_wd \<Longrightarrow> (2::nat) ^ limb_wd = 2 ^ k * 2 ^ (limb_wd - k)"
  apply (rewrite in "2 ^ limb_wd" k_decomp[of k])
  apply simp
  apply simp
  apply (rewrite monoid_mult_class.power_add)
  by blast

lemma mul_k_pow_simp: "0 < k \<Longrightarrow> k < limb_wd \<Longrightarrow> (x * (2::nat) ^ k) div 2 ^ limb_wd = x div 2 ^ (limb_wd - k)"
  by (simp add: k_pow_decomp)

lemma limbs_bit_shift_zero: "limbs_bit_shift 0 a b = a" unfolding limbs_bit_shift_def limb_wd_def
  by (simp add: shiftr_eq_0)

find_theorems "to_bl"
term "word_clz"

find_theorems "word_clz" "msb"

lemma clz_zero_msb: "word_clz a = 0 \<Longrightarrow> msb a"
  by (metis add.right_neutral bit_word_log2 diff_diff_left lens_not_0 msb_nth word_clz_0 word_log2_def wsst_TYs(3))

lemma clz_lt_width: "(a::limb) \<noteq> 0 \<Longrightarrow> word_clz a < limb_wd"
  using word_clz_nonzero_max
  by (metis word_clz_nonzero_max wsst_TYs(3) limb_wd_def)

lemma msb_iff: "limb_nat l \<ge> limb_sz div 2 \<longleftrightarrow> msb l"
  unfolding limb_sz_unfold limb_nat_def
  by (simp add: msb_unat_big)


find_theorems "bit" "shiftl"

find_theorems "msb" "(||)"

lemma "a \<noteq> 0 \<Longrightarrow> msb (limbs_bit_shift (word_clz a) a b) = True" 
  unfolding limbs_bit_shift_def  
  using msb_shiftl_clz[of a] word_ops_msb
  by blast

definition "normalize_msb ai clz \<equiv> doN {
  ASSERT (clz < limb_wd);

  let l = length ai;

  if l = 0 then RETURN big_int0 else doN {
    ASSERT (l > 0);
  
    let rs = big_int0;
  
    ai_first \<leftarrow> get_or_zero_fast ai 0;
    let ai_first_shift = limbs_bit_shift clz ai_first 0;
    
    rs \<leftarrow> bi_append rs ai_first_shift;
  
  
    rs \<leftarrow> forI 
      (\<lambda>i rs. length rs = i \<and> big_int_\<alpha> rs = (big_int_\<alpha> (take i ai) * 2 ^ clz) mod limb_sz ^ i)
      1 l 
      (\<lambda>i rs. doN {
        h \<leftarrow> get_or_zero_fast ai i;
        l \<leftarrow> get_or_zero_fast ai (i-1);
        let h_shift = limbs_bit_shift clz h l;
        rs \<leftarrow> bi_append rs h_shift;
        RETURN rs
      }) rs;
  
    RETURN rs
  }
}"

find_theorems "limb_nat" "limbs_bit_shift" 
lemma "k < limb_wd \<Longrightarrow> limb_nat (limbs_bit_shift k a b) = 
  (limb_nat a * 2 ^ k + limb_nat b div 2 ^ (limb_wd - k)) mod limb_sz"
  unfolding limbs_bit_shift_bit_list'[of k a b]
  oops


lemma normalize_msb_correct: "clz < limb_wd \<Longrightarrow> 
  (ai, a) \<in> big_int_rel \<Longrightarrow> normalize_msb ai clz \<le> (\<Down> big_int_rel) (RETURN (a * 2 ^ clz))"
  unfolding normalize_msb_def get_or_zero_fast_def big_int0_def
  apply (refine_vcg bi_append_correct) 
  subgoal using big_int_length_zero_rel' by force
  apply simp_all
  subgoal unfolding limbs_bit_shift_def
    by (simp add: limb_bit_shift_left take_Suc_conv_app_nth)
  apply clarsimp
  subgoal for res proof - 
    define idx where "idx = length res"
    assume "big_int_\<alpha> res = big_int_\<alpha> (take (length res) ai) * 2 ^ clz mod limb_sz ^ length res"
    assume "res \<noteq> []" and "length res - Suc 0 \<le> length ai" 
    hence "idx \<ge> 1" and "idx - 1 \<le> length ai" using idx_def by auto


    have "big_int_\<alpha> (res @ [limbs_bit_shift clz (ai ! length res) (ai ! (length res - Suc 0))]) = 
      big_int_\<alpha> res + limb_nat (limbs_bit_shift clz (ai ! length res) (ai ! (length res - Suc 0)))
         * limb_sz ^ length res" 
      using big_int_to_nat_snoc by blast
  (*    also have "... = big_int_\<alpha> res + " *)
    oops




(* HERE *)

definition bits_bool :: "limb \<Rightarrow> bool list"
  where "bits_bool l \<equiv> map (bit l) [0..<limb_wd]"

definition bits_base :: "limb \<Rightarrow> nat list"
  where "bits_base l \<equiv> map (\<lambda> b. if (bit l b) then 1 else 0) [0..<limb_wd]"

lemma bit_list: "bits_bool l = rev (to_bl l)"
  unfolding bits_bool_def 
  by (metis limb_wd_def rev_to_bl_eq)

lemma "bits_base l = map (\<lambda>b. if b then 1 else 0) (bits_bool l)"
  unfolding bits_base_def bits_bool_def by simp

global_interpretation base2: base_decomp 2
  defines decomp2 = "base_decomp.base_decomp 2"
      and digits2 = "base_decomp.digits 2"
      and bvalue2 = "base_decomp.base_value 2"
  by unfold_locales (simp_all add:base_decomp_def)

definition bit_indices :: "limb \<Rightarrow> nat list" 
  where "bit_indices l \<equiv> filter (\<lambda> b. l !! b) [0..<limb_wd]"

lemma bits_lt: "List.member (bit_indices l) b \<Longrightarrow> b < limb_wd"
  unfolding bit_indices_def by auto


lemma limb_nat_lt: "limb_nat x < 2 ^ limb_wd"
  using limb_nat_lt limb_sz_def by presburger

lemma digits2_lt_limb_wd: "digits2 (limb_nat x) \<le> limb_wd"
  using base2.base_pow_lt_digits limb_nat_lt by presburger
  



definition bits_val :: "nat list \<Rightarrow> nat"
  where "bits_val s \<equiv> fold (+) (map (\<lambda>x. 2 ^ x) s) 0"




(* What we need next is that the highest limb of b in a div b is \<ge> limb_sz div 2 *)
(* This allows us to simplify the division to only 2 limbs by 1 limb *)



(*

Now the idea is to basically emulate the long division algorithm you
know from primary school: if the divisor y has n limbs, we take the
first (n+1) limbs of the dividend (call it x'), and compute (q, r) :=
divmod(x', y). Then the quotient q is the highest limb of our output and
(r * b) plus the next limb of x is our new x', and so on.

The interesting question is how to compute divmod(x', y). This is pretty
much the only interesting part of the algorithm. The idea is to compute
an approximation to (x' div y) by dividing the highest 2 limbs of x' by
the highest limb of y (which is a 2-by-1 division that CPUs implement in
hardware, i.e. we can assume that this is given). This approximation is
either equal to the true value or 1 or 2 smaller than the true value. So   (TODO: smaller or bigger?)
you have to do some extra work to detect this possibility and correct it
if need be (you can detect this situation by noticing that the computed
remainder will be \<ge> b, which is not allowed). This step only works if
the highest bit of the highest divisor limb is 1, so that's why we need
to do the normalisation in the beginning.

I'm sure there are various sources other than Knuth online that explain
this algorithm in detail. You might also want to look at the GMP
implementation and documentation:
https://gmplib.org/manual/Basecase-Division


There's a bunch of optimisations that you can do, e.g. a
"divide-and-conquer" version of the algorithm that basically runs the
above algorithm with b not being the limb size, but many limbs, and then
implementing the "2-by-1" division as a recursive call. See GMP again:
https://gmplib.org/manual/Divide-and-Conquer-Division

The nice thing about this divide-and-conquer division is that it has
running time roughly equivalent to O(M(n)), where M(n) is the complexity
of multiplication. So implementing a faster multiplication algorithm
automatically gives you a faster division algorithm.


Since you already have naïve multiplication and Karatsuba
multiplication, I don't think verifying either of these should be very
hard for you algorithmically. It does require some elementary
mathematical lemmas.


The fastest division algorithms work by computing a fixed-point
approximation of 1/y via something like Newton iteration and then just
multiplying that with x. Would be nice to have, but probably
considerably more work, so I wouldn't recommend it for now. See:
https://gmplib.org/manual/Block_002dWise-Barrett-Division
 *)

end
