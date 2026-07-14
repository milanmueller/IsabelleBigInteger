theory LLVM_CodeGen_Signed
  imports Arithmetics "../LLVM_CodeGen" LLVM_CodeGen_Auxiliary UnsignedArithmetics
begin

section "Comparisons"

sepref_register "op_neq :: bool \<Rightarrow> _"
sepref_def signed_big_int_eq_impl is "uncurry signed_big_int_eq"
  :: \<open>sbi_aux_assn\<^sup>k *\<^sub>a sbi_aux_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding signed_big_int_eq_def
  apply (annot_snat_const size_t)
  by sepref

sepref_def signed_big_int_neq_impl is "uncurry signed_big_int_neq"
  :: "sbi_aux_assn\<^sup>k *\<^sub>a sbi_aux_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding signed_big_int_neq_def
  by sepref

section "Constants"

sepref_def signed_big_int0_impl is "uncurry0 (RETURN signed_big_int0)"
  :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a sbi_aux_assn"
  unfolding signed_big_int0_def
  apply (rewrite al_fold_custom_empty[where 'l=size_t])
  by sepref

lemma signed_big_int1_alt:
  "signed_big_int1 = (op_al_empty TYPE(size_t) @ [1], False)"
  by (simp add: signed_big_int1_def)

sepref_def signed_big_int1_impl is "uncurry0 (RETURN signed_big_int1)"
  :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a sbi_aux_assn"
  unfolding signed_big_int1_alt
  by sepref

section "Unsigned Arithmetics"

sepref_def signed_big_int_add_loop_impl is "uncurry2 signed_big_int_add_loop"
  :: "sbi_aux_assn\<^sup>k *\<^sub>a sbi_aux_assn\<^sup>k *\<^sub>a limb_assn\<^sup>k \<rightarrow>\<^sub>a bi_aux_assn"
  unfolding signed_big_int_add_loop_def signed_big_int_add_cond_def
  apply (annot_snat_const size_t)
  by sepref

sepref_def signed_big_int_abs_add_impl is "uncurry signed_big_int_abs_add"
  :: "sbi_aux_assn\<^sup>k *\<^sub>a sbi_aux_assn\<^sup>k \<rightarrow>\<^sub>a bi_aux_assn"
  unfolding signed_big_int_abs_add_def
  by sepref

sepref_def signed_big_int_abs_leq_impl is "uncurry signed_big_int_abs_leq"
  :: "sbi_aux_assn\<^sup>k *\<^sub>a sbi_aux_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding signed_big_int_abs_leq_def
  apply (annot_snat_const size_t)
  by sepref

sepref_def signed_big_int_abs_compl_impl is "uncurry signed_big_int_abs_compl"
  :: "sbi_aux_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a bi_aux_assn"
  unfolding signed_big_int_abs_compl_def compl_def compl_cond_def
  apply (annot_snat_const size_t)
  by sepref

sepref_def signed_big_int_add_inc_impl is "uncurry signed_big_int_add_inc"
  :: "sbi_aux_assn\<^sup>k *\<^sub>a sbi_aux_assn\<^sup>k \<rightarrow>\<^sub>a bi_aux_assn"
  unfolding signed_big_int_add_inc_def
  by sepref

sepref_register signed_big_int_add_inc

sepref_def signed_big_int_sub_abs_compl_impl is "uncurry signed_big_int_sub_abs_compl"
  :: "sbi_aux_assn\<^sup>k *\<^sub>a sbi_aux_assn\<^sup>k \<rightarrow>\<^sub>a bi_aux_assn"
  unfolding signed_big_int_sub_abs_compl_def  
  by sepref
  

(* TODO: We don't acutally need to refine this one *)
sepref_def signed_big_int_add_\<sigma>_eq_impl is "uncurry signed_big_int_add_\<sigma>_eq"
  :: "sbi_aux_assn\<^sup>k *\<^sub>a sbi_aux_assn\<^sup>k \<rightarrow>\<^sub>a sbi_aux_assn"
  unfolding signed_big_int_add_\<sigma>_eq_def
  by sepref

sepref_def signed_big_int_add_\<sigma>_neq_impl is "uncurry signed_big_int_add_\<sigma>_neq"
  :: "sbi_aux_assn\<^sup>k *\<^sub>a sbi_aux_assn\<^sup>k \<rightarrow>\<^sub>a sbi_aux_assn"
  unfolding signed_big_int_add_\<sigma>_neq_def
  by sepref

sepref_def signed_big_int_add_impl is "uncurry signed_big_int_add"
  :: "sbi_aux_assn\<^sup>k *\<^sub>a sbi_aux_assn\<^sup>k \<rightarrow>\<^sub>a sbi_aux_assn"
  unfolding signed_big_int_add_def
  by sepref


section "Subtraction"
sepref_def signed_big_int_inv is "RETURN o signed_big_int_inv"
  :: "sbi_aux_assn\<^sup>k \<rightarrow>\<^sub>a sbi_aux_assn"
  unfolding signed_big_int_inv_def 
  apply sepref_dbg_keep
  oops
  (* For now only works destructively *)

section "Multiplication"
sepref_def signed_big_int_mult_limb_aux_impl is "uncurry signed_big_int_mult_limb_aux"
  :: "sbi_aux_assn\<^sup>k *\<^sub>a limb_assn\<^sup>k \<rightarrow>\<^sub>a bi_aux_assn"
  unfolding signed_big_int_mult_limb_aux_def
  apply (annot_snat_const size_t)
  by sepref

sepref_def signed_big_int_mult_limb_impl is "uncurry signed_big_int_mult_limb"
  :: "sbi_aux_assn\<^sup>k *\<^sub>a limb_assn\<^sup>k \<rightarrow>\<^sub>a bi_aux_assn"
  unfolding signed_big_int_mult_limb_def
  by sepref

lemma check_empty_alt: "(ci :: big_int) \<noteq> [] \<equiv> length ci \<noteq> 0" by auto

sepref_def signed_big_int_mult_school_impl is "uncurry signed_big_int_mult_school"
  :: "sbi_aux_assn\<^sup>k *\<^sub>a sbi_aux_assn\<^sup>k \<rightarrow>\<^sub>a sbi_aux_assn"
  unfolding signed_big_int_mult_school_def signed_big_int_mult_school_aux_def
  unfolding signed_big_int_mult_school_cond_def signed_big_int_mult_school_body_def
  unfolding check_empty_alt
  apply (rewrite al_fold_custom_empty[where 'l=size_t])
  apply (annot_snat_const size_t)
  by sepref
    
subsection \<open>Inversion\<close>

sepref_def sbi_inv_impl is \<open>RETURN o sbi_inv\<close>
  :: \<open>sbi_aux_assn\<^sup>d \<rightarrow>\<^sub>a sbi_aux_assn\<close>
  unfolding sbi_inv_def
  by sepref

section \<open>Sepref Registrations\<close>
text \<open>Now we register our implementations to refine HOL integers through @{term sbi_assn}\<close>

sepref_register "0 :: int"
sepref_register "1 :: int"

context
  notes [fcomp_norm_unfold] = sbi_assn_def[symmetric]
begin

lemmas signed_big_int_eq_impl_hnr[sepref_fr_rules] =
  signed_big_int_eq_impl.refine[FCOMP signed_big_int_eq_refine]

lemmas signed_big_int_neq_impl_hnr[sepref_fr_rules] =
  signed_big_int_neq_impl.refine[FCOMP signed_big_int_neq_refine]

lemmas signed_big_int0_impl_hnr[sepref_fr_rules] =
  signed_big_int0_impl.refine[FCOMP signed_big_int0_refine]

lemmas signed_big_int1_impl_hnr[sepref_fr_rules] =
  signed_big_int1_impl.refine[FCOMP signed_big_int1_refine]

lemmas signed_big_int_add_hnr[sepref_fr_rules] =
  signed_big_int_add_impl.refine[FCOMP signed_big_int_add_refine]

(* TODO: at some point this should probably be the more efficient Karatsuba implementation? *)
lemmas signed_big_int_mult_school_hnr[sepref_fr_rules] =
  signed_big_int_mult_school_impl.refine[FCOMP signed_big_int_mult_school_refine]

lemmas sbi_inv_hnr[sepref_fr_rules] =
  sbi_inv_impl.refine[FCOMP sbi_inv_ref]

end

text \<open>Deallocation of sbi temporaries (needed whenever a synthesis creates
  intermediate sbi values, e.g. in \<open>n + m \<noteq> 0\<close>).\<close>
schematic_goal sbi_assn_free[sepref_frame_free_rules]: "MK_FREE sbi_assn ?fr"
  unfolding sbi_assn_def
  by (rule MK_FREE_hrcompI mk_free_pair al_assn_free mk_free_pure mk_free_is_pure)+

end
