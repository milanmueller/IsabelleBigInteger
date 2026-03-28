theory IsabelleCodeGen
  imports Main "Karatsuba" "Setup"
begin

definition "has_res c m \<equiv> c \<noteq> dSUCCEED \<and> nres_of c \<le> m"
lemma has_resI[refine_transfer]: "\<lbrakk>nres_of c \<le> m; c \<noteq> dSUCCEED\<rbrakk> \<Longrightarrow> has_res c m"
	unfolding has_res_def by auto

lemma has_resD:
	assumes "has_res c m"
	shows "c \<noteq> dSUCCEED" "nres_of c \<le> m"
	using assms unfolding has_res_def by auto

find_theorems "mop_list_butlast"

synth_definition big_int_trim_code is "has_res \<hole> (big_int_trim a)"
	unfolding big_int_trim_def mop_list_butlast_alt
	by refine_transfer

lemmas [refine_transfer] = has_resD[OF big_int_trim_code.refine]

synth_definition big_int_add_loop_code is "has_res \<hole> (big_int_add_loop a b c)"
  unfolding big_int_add_loop_def bi_append_def using sepref_sorry
  by refine_transfer
   
lemmas [refine_transfer] = has_resD[OF big_int_add_loop_code.refine]

synth_definition big_int_rshift_code is "has_res \<hole> (big_int_rshift i a)"
  unfolding big_int_rshift_def
  by refine_transfer

lemmas [refine_transfer] = has_resD[OF big_int_rshift_code.refine]

synth_definition big_int_add_code is "has_res \<hole> (big_int_add a b)"
	unfolding big_int_add_def 
	by refine_transfer
lemmas [refine_transfer] = has_resD[OF big_int_add_code.refine]

synth_definition big_int_add_inc_code is "has_res \<hole> (big_int_add_inc a b)"
	unfolding big_int_add_inc_def 
	by refine_transfer
lemmas [refine_transfer] = has_resD[OF big_int_add_inc_code.refine]


synth_definition big_int_mult_school_code is "has_res \<hole> (big_int_mult_school a b)"
	unfolding big_int_mult_school_def big_int_mult_school_invar_def 
	  big_int_mult_school_cond_def big_int_mult_school_body_def 
	  big_int_mult_limb_def  big_int_mult_limb_aux_def big_int0_def bi_append_def
	using sepref_sorry
	by refine_transfer

lemmas [refine_transfer] = has_resD[OF big_int_mult_school_code.refine]

synth_definition big_int_compl_code is "has_res \<hole> (big_int_compl ai l)"
	unfolding big_int_compl_def bi_append_def
	using sepref_sorry
	by refine_transfer
lemmas [refine_transfer] = has_resD[OF big_int_compl_code.refine]

synth_definition big_int_mult_limb_aux_code is "has_res \<hole> (big_int_mult_limb_aux ai bix)"
	unfolding big_int_mult_limb_aux_def bi_append_def
  using sepref_sorry
	by refine_transfer
lemmas [refine_transfer] = has_resD[OF big_int_mult_limb_aux_code.refine]

synth_definition big_int_small_to_limb_code is "has_res \<hole> (big_int_small_to_limb ai)"
  unfolding big_int_small_to_limb_def by refine_transfer
lemmas [refine_transfer] = has_resD[OF big_int_small_to_limb_code.refine]

synth_definition big_int_mult_limb is "has_res \<hole> (big_int_mult_limb ai b)"
  unfolding big_int_mult_limb_def by refine_transfer
lemmas [refine_transfer] = has_resD[OF big_int_mult_limb.refine]

synth_definition big_int_mult_small_code is "has_res \<hole> (big_int_mult_small ai bi)"
  unfolding big_int_mult_small_def by refine_transfer
lemmas [refine_transfer] = has_resD[OF big_int_mult_small_code.refine]


synth_definition remove_last_limb_code is "has_res \<hole> (remove_last_limb ai)"
	unfolding remove_last_limb_def
	by refine_transfer
lemmas [refine_transfer] = has_resD[OF remove_last_limb_code.refine]


synth_definition big_int_take_code is "has_res \<hole> (big_int_take l ai)"
	unfolding big_int_take_def
	by refine_transfer
lemmas [refine_transfer] = has_resD[OF big_int_take_code.refine]

synth_definition big_int_sub_compl_code is "has_res \<hole> (big_int_sub_compl ai bi)"
	unfolding big_int_sub_compl_def
	by refine_transfer
lemmas [refine_transfer] = has_resD[OF big_int_sub_compl_code.refine]

synth_definition karatsuba_code is "has_res \<hole> (karatsuba ai bi)"
	unfolding karatsuba_def big_int_mult_limb_def big_int_drop_def big_int_take_def big_int_rshift_def karatsuba_RECT_base_def karatsuba_aux_def karatsuba_recurse_def
	by refine_transfer 
lemmas [refine_transfer] = has_resD[OF karatsuba_code.refine]

lemma has_res_combine: 
	assumes "has_res c a"
	assumes "a \<le> \<Down>R (SPEC Q)"
	shows "\<exists>ri r. c = dRETURN ri \<and> (ri,r)\<in>R \<and> Q r"
	using assms unfolding has_res_def
	apply (cases c; simp)
	by (auto simp: pw_le_iff refine_pw_simps)

lemma karatsuba_code_correct:
	assumes "(ai,a)\<in>big_int_rel" "(bi,b)\<in>big_int_rel" 
	shows "\<exists>ci c. karatsuba_code ai bi = dRETURN ci \<and> (ci, c) \<in> big_int_rel \<and> c = (a*b)"
	apply (rule has_res_combine[OF karatsuba_code.refine])
	using assms karatsuba_correct
	by (simp add: RETURN_SPEC_conv)

fun make_big_int :: "nat \<Rightarrow> big_int" 
  where "make_big_int n = replicate n (-1)"
	

prepare_code_thms [code] karatsuba_code_def big_int_mult_school_code_def
print_theorems

value "big_int_\<gamma> (big_int_\<alpha> [1,1,1, 1] * big_int_\<alpha> [1,1,1, 1]) = (the_res (karatsuba_code [1,1,1, 1] [1,1,1, 1]))"

value "length (the_res (karatsuba_code (replicate 400 (-1)) (replicate 400 (-1))))"

value "length (the_res (big_int_mult_school_code (replicate 200 (-1)) (replicate 100 (-1))))"
	
export_code karatsuba_code big_int_mult_school_code make_big_int nat_of_integer the_res 
  in Haskell module_name BigInt fi le "eval"

end