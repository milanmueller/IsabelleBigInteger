theory LLVM_CodeGen_Signed
  imports SignedBigInt LLVM_CodeGen
begin

(* TODO: Move everything in here into the main LLVM_CodeGen theory *)
abbreviation "char_assn \<equiv> word_assn' TYPE(8)"

(* `sbi` \<sim> "signed big integer" *)
abbreviation "sbi_aux_assn \<equiv> char_assn \<times>\<^sub>a bi_aux_assn"
definition "sbi_assn \<equiv> hr_comp sbi_aux_assn signed_big_int_rel"


term bi_aux_assn
(* "al_assn word_assn" :: "64 word list \<Rightarrow> 64 word \<times> 64 word \<times> 64 word ptr \<Rightarrow> llvm_amemory \<Rightarrow> bool" *)

(* here i'm just copy pasting stuff from the main llvm theory *)
lemmas [safe_constraint_rules] = CN_FALSEI[of is_pure sbi_assn]

(* This part does not work with the tuple
lemma sbi_assn_free[sepref_frame_free_rules]: "MK_FREE sbi_assn (arl_free)"
*)

context
  notes [fcomp_norm_unfold] = sbi_assn_def[symmetric]
begin

sepref_def \<sigma>_impl is "RETURN o \<sigma>" :: "sbi_aux_assn\<^sup>k \<rightarrow>\<^sub>a char_assn"
  unfolding \<sigma>_def fst_def
  by sepref

thm limbs_of_def

sepref_def \<l>imbs_of_impl is "RETURN o limbs_of" :: "sbi_aux_assn\<^sup>k \<rightarrow>\<^sub>a bi_aux_assn"
  unfolding limbs_of_def snd_def
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

lemma signed_big_int_add_alt:
  "signed_big_int_add ai bi = do {
    let ((\<sigma>\<^sub>a, lsa), (\<sigma>\<^sub>b, lsb)) = (ai, bi);
    if \<sigma>\<^sub>a = \<sigma>\<^sub>b then do {
      ci \<leftarrow> big_int_add lsa lsb;
      RETURN (\<sigma>\<^sub>a, ci)
    } else do {
      let pos_l = (if \<sigma>\<^sub>a = 0 then lsa else lsb);
      let neg_l = (if \<sigma>\<^sub>a = 0 then lsb else lsa);
      pos_lt \<leftarrow> big_int_lt pos_l neg_l;
      if pos_lt then do {
        (ci, _) \<leftarrow> big_int_sub neg_l pos_l;
        RETURN (1, ci)
      } else do {
        (ci, _) \<leftarrow> big_int_sub pos_l neg_l;
        RETURN (0, ci)
      }
    }
  }"
  unfolding signed_big_int_add_def \<sigma>_def limbs_of_def
  by (cases ai; cases bi; simp)

sepref_register big_int_add
sepref_register big_int_sub
sepref_register big_int_lt

sepref_def signed_big_int_add_impl is "uncurry signed_big_int_add"
  :: "sbi_aux_assn\<^sup>k *\<^sub>a sbi_aux_assn\<^sup>k \<rightarrow>\<^sub>a sbi_aux_assn"
  unfolding signed_big_int_add_alt limbs_of_def snd_def
  apply sepref_dbg_keep
  apply sepref_dbg_trans_keep
  apply sepref_dbg_trans_step_keep
  apply sepref_dbg_side_unfold
  apply clarsimp

  (*
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
  *)


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

end (* of context *)
end
