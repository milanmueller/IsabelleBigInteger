theory LLVM_CodeGen_Signed
  imports SignedBigInt LLVM_CodeGen
begin

(* `sbi` \<sim> "signed big integer" *)
abbreviation "sbi_aux_assn \<equiv> bi_aux_assn \<times>\<^sub>a bool1_assn"
definition "sbi_assn \<equiv> hr_comp sbi_aux_assn signed_big_int_rel"

(* "al_assn word_assn" :: "64 word list \<Rightarrow> 64 word \<times> 64 word \<times> 64 word ptr \<Rightarrow> llvm_amemory \<Rightarrow> bool" *)

(* here i'm just copy pasting stuff from the main llvm theory *)
(* lemmas [safe_constraint_rules] = CN_FALSEI[of is_pure sbi_assn] *)

(* This part does not work with the tuple
lemma sbi_assn_free[sepref_frame_free_rules]: "MK_FREE sbi_assn (arl_free)"
*)

(*
context
  notes [fcomp_norm_unfold] = sbi_assn_def[symmetric]
begin
*)

sepref_def \<sigma>_impl is "RETURN o \<sigma>" :: "sbi_aux_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding \<sigma>_def snd_def
  by sepref

definition signed_big_int_abs_lt :: "signed_big_int \<Rightarrow> signed_big_int \<Rightarrow> bool nres" where
  "signed_big_int_abs_lt ai bi = do {
    let ((limbs\<^sub>a, _),(limbs\<^sub>b, _)) = (ai, bi);
    big_int_lt limbs\<^sub>a limbs\<^sub>b
  }"

definition signed_big_int_abs_add :: "signed_big_int \<Rightarrow> signed_big_int \<Rightarrow> big_int nres" where
  "signed_big_int_abs_add ai bi = do {
    let ((limbs\<^sub>a, _),(limbs\<^sub>b, _)) = (ai, bi);
    big_int_add limbs\<^sub>a limbs\<^sub>b
  }"

(* NOTE: this assumes ai \<ge> bi, otherwise returns limb_sz^l - a + b *)
definition signed_big_int_abs_sub :: "signed_big_int \<Rightarrow> signed_big_int \<Rightarrow> big_int nres" where
  "signed_big_int_abs_sub ai bi = do {
    let ((limbs\<^sub>a, _),(limbs\<^sub>b, _)) = (ai, bi);
    big_int_sub_compl limbs\<^sub>a limbs\<^sub>b 
  }"

definition signed_big_int_length :: "signed_big_int \<Rightarrow> nat" where
  "signed_big_int_length ai \<equiv> length $ limbs_of ai"

sepref_def signed_big_int_length_impl is "RETURN o signed_big_int_length"
  :: "sbi_aux_assn\<^sup>d \<rightarrow>\<^sub>a size_assn"
  unfolding signed_big_int_length_def limbs_of_def fst_def
  by sepref

sepref_def signed_big_int_abs_lt_impl is "uncurry signed_big_int_abs_lt"
  :: "sbi_aux_assn\<^sup>d *\<^sub>a sbi_aux_assn\<^sup>d \<rightarrow>\<^sub>a bool1_assn"
  unfolding signed_big_int_abs_lt_def
  by sepref

sepref_def signed_big_int_abs_add_impl is "uncurry signed_big_int_abs_add"
  :: "sbi_aux_assn\<^sup>d *\<^sub>a sbi_aux_assn\<^sup>d \<rightarrow>\<^sub>a bi_aux_assn"
  unfolding signed_big_int_abs_add_def
  by sepref

sepref_def signed_big_int_abs_sub_imp is "uncurry signed_big_int_abs_sub"
  :: "sbi_aux_assn\<^sup>d *\<^sub>a sbi_aux_assn\<^sup>d \<rightarrow>\<^sub>a bi_aux_assn"
  unfolding signed_big_int_abs_sub_def
  by sepref

(*
    *TODO: anstatt zu destrukturieren, wrapper für die arithmetischen funktionen von Mihai schreiben.
    *TODO: die tatsächlich nach LLVM verfeinerte subtraktion nutzen. \<rightarrow> evtl. big_int_sub_compl 
*)

sepref_def signed_big_int_add_impl is "uncurry signed_big_int_add"
  :: "sbi_aux_assn\<^sup>d *\<^sub>a sbi_aux_assn\<^sup>d \<rightarrow>\<^sub>a sbi_aux_assn"
  unfolding signed_big_int_add_def limbs_of_def fst_def
  (*
  apply sepref_dbg_keep
  apply sepref_dbg_trans_keep
  apply sepref_dbg_trans_step_keep
  apply sepref_dbg_side_unfold
  apply clarsimp
  *)
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve_cp
  apply sepref_dbg_constraints
  oops


(*

sepref_def signed_big_int_add_impl is "uncurry signed_big_int_add"
  :: "sbi_aux_assn\<^sup>k *\<^sub>a sbi_aux_assn\<^sup>k \<rightarrow>\<^sub>a sbi_aux_assn"
  unfolding signed_big_int_add_def \<sigma>_def limbs_of_def fst_def snd_def
  apply sepref_dbg_keep
  apply sepref_dbg_trans_keep
  apply sepref_dbg_trans_step_keep
  apply sepref_dbg_side_unfold
  apply clarsimp
  oops
*)

(* end (* of context *) *)
end
