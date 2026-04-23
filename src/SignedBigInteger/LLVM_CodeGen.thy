theory LLVM_CodeGen
  imports Arithmetics "../LLVM_CodeGen" LLVM_CodeGen_Auxiliary UnsignedArithmetics
begin

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

sepref_register "op_neq :: bool \<Rightarrow> _"
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

end
