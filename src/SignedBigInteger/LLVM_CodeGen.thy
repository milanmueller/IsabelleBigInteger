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

sepref_def signed_big_int_mult_school_body_impl is "uncurry2 signed_big_int_mult_school_body"
  :: "sbi_aux_assn\<^sup>k *\<^sub>a sbi_aux_assn\<^sup>k *\<^sub>a (bi_aux_assn\<^sup>k *\<^sub>a size_assn\<^sup>k) \<rightarrow>\<^sub>a bi_aux_assn \<times>\<^sub>a size_assn"
  unfolding signed_big_int_mult_school_body_def signed_big_int_mult_school_cond_def
  apply (annot_snat_const size_t)
  apply sepref_dbg_keep
  apply sepref_dbg_trans_keep
  apply sepref_dbg_trans_step_keep
  supply [[unify_trace_failure]]
  apply sepref_dbg_trans_step_keep
  oops

sepref_def signed_big_int_mult_school_impl


(* OLD

sepref_def \<sigma>_impl is "RETURN o \<sigma>" :: "sbi_aux_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding \<sigma>_def snd_def
  by sepref

sepref_def limbs_of_impl is "RETURN o limbs_of" :: "sbi_aux_assn\<^sup>d \<rightarrow>\<^sub>a bi_aux_assn"
  unfolding limbs_of_def fst_def
  by sepref

definition signed_big_int_abs_lt :: "signed_big_int \<Rightarrow> signed_big_int \<Rightarrow> bool nres" where
  "signed_big_int_abs_lt ai bi = do {
    let ((limbs\<^sub>a, _),(limbs\<^sub>b, _)) = (ai, bi);
    big_int_lt limbs\<^sub>a limbs\<^sub>b
  }"

definition signed_big_int_abs_lt_test :: "big_int \<Rightarrow> big_int \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool nres" where
  "signed_big_int_abs_lt_test ai bi b c = do {
    big_int_lt ai bi
  }"
sepref_def signed_big_int_length_impl is "uncurry3 signed_big_int_abs_lt_test"
  :: "bi_aux_assn\<^sup>k *\<^sub>a bi_aux_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding signed_big_int_abs_lt_test_def
  by sepref


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

(*
sepref_def signed_big_int_length_impl is "RETURN o signed_big_int_length"
  :: "sbi_aux_assn\<^sup>d \<rightarrow>\<^sub>a size_assn"
  unfolding signed_big_int_length_def limbs_of_def fst_def
  by sepref
*)

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

definition signed_big_int_add_aux :: "big_int \<Rightarrow> big_int \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> big_int nres" where
  "signed_big_int_add_aux limbs\<^sub>a limbs\<^sub>b \<sigma>\<^sub>a \<sigma>\<^sub>b = do {
    if \<sigma>\<^sub>a \<noteq> \<sigma>\<^sub>b then do {
      a_lt_b \<leftarrow> big_int_lt limbs\<^sub>a limbs\<^sub>b;
      if a_lt_b then
        big_int_sub_compl limbs\<^sub>b limbs\<^sub>a
      else
        big_int_sub_compl limbs\<^sub>a limbs\<^sub>b
    } else do {
      big_int_add limbs\<^sub>a limbs\<^sub>b
    }
  }"

definition signed_big_int_add :: "signed_big_int \<Rightarrow> signed_big_int \<Rightarrow> big_int nres" where
  "signed_big_int_add ai bi \<equiv> do {
    let (\<sigma>\<^sub>a, \<sigma>\<^sub>b) = (\<sigma> ai, \<sigma> bi);
    let (limbs\<^sub>a, limbs\<^sub>b) = (limbs_of ai, limbs_of bi);
    signed_big_int_add_aux limbs\<^sub>a limbs\<^sub>b \<sigma>\<^sub>a \<sigma>\<^sub>b
  }"

term "TYPE(1)"
term "sbi_aux_assn\<^sup>d *\<^sub>a sbi_aux_assn\<^sup>d \<rightarrow>\<^sub>a sbi_aux_assn"
term "sbi_aux_assn\<^sup>k *\<^sub>a sbi_aux_assn\<^sup>k \<rightarrow>\<^sub>a sbi_aux_assn"


term "uncurry3 signed_big_int_add_aux"        
sepref_def signed_big_int_add_aux_impl is "uncurry3 signed_big_int_add_aux"
  :: "bi_aux_assn\<^sup>k *\<^sub>a bi_aux_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k *\<^sub>a bool1_assn\<^sup>k \<rightarrow>\<^sub>a bi_aux_assn"
  unfolding signed_big_int_add_aux_def
  by sepref

sepref_def signed_big_int_add_impl is "uncurry signed_big_int_add"
  :: "sbi_aux_assn\<^sup>d *\<^sub>a sbi_aux_assn\<^sup>d \<rightarrow>\<^sub>a bi_aux_assn"
  unfolding signed_big_int_add_def
  by sepref

sepref_def big_int_mult_school_impl is "uncurry big_int_mult_school"
  :: "bi_aux_assn\<^sup>k *\<^sub>a bi_aux_assn\<^sup>k \<rightarrow>\<^sub>a bi_aux_assn"
  unfolding big_int_mult_school_def big_int_mult_school_cond_def big_int_mult_school_body_def
  apply (annot_snat_const size_t)
  apply sepref_dbg_keep
  apply sepref_dbg_trans_keep
  apply sepref_dbg_trans_step_keep
  apply sepref_dbg_side_unfold
  (* need non-overflow proof which might have to do with special LLVM sorry *)
  oops


sepref_def signed_big_int_mult_impl is "uncurry signed_big_int_mult"
  :: "sbi_aux_assn\<^sup>d *\<^sub>a sbi_aux_assn\<^sup>d \<rightarrow>\<^sub>a sbi_aux_assn"
  unfolding signed_big_int_mult_def \<sigma>_mult_def
  apply sepref_dbg_keep
  apply sepref_dbg_trans_keep
  apply sepref_dbg_trans_step_keep
  apply sepref_dbg_side_unfold
  (* need to refine big_int_mult_school *)
  oops

(*you need this for the base operations*)
definition length_fst where
  \<open>length_fst a = length (fst a)\<close>

term sbi_aux_assn

definition length_fst_impl :: \<open>(64 word \<times> 64 word \<times> 64 word ptr) \<times> 1 word \<Rightarrow> 64 word llM\<close> where [llvm_code,llvm_inline]:
  \<open>length_fst_impl = (\<lambda>al. 
    let ((l,c,a),_) = al in Mreturn l
  )\<close>

(*I thought this would just work out of the box with sepref*)
lemma [sepref_fr_rules]:
  \<open>(length_fst_impl, RETURN o length_fst) \<in> sbi_aux_assn\<^sup>k  \<rightarrow>\<^sub>a snat_assn\<close>
  unfolding length_fst_def length_fst_impl_def
  apply sepref_to_hoare
  apply vcg_all
  apply (auto simp: ENTAILS_def pure_true_conv) 
  (*usually super ugly*)
  sorry

definition get_at_fst where "get_at_fst ai i = ai ! i"

(*
definition get_at_fst_impl :: "((64 word \<times> 64 word \<times> 64 word ptr) \<times> 1 word) \<times> 64 word \<Rightarrow> 64 word llM" where [llvm_code,llvm_inline]:
  "get_at_fst_impl = (\<lambda>(ai, i).
    let (((l,c,a),_),i) = (ai, i) in Mreturn ... 
  )"
*)

term length_fst_impl
sepref_register length_fst_impl

(*not working for reasons: TODO Mathias*)
export_llvm length_fst_impl file "/tmp/test.ll"

definition get_or_zero_fst where
  \<open>get_or_zero_fst a b = get_or_zero (fst a) b\<close>

lemma get_or_zero_fst_alt_def:
  "get_or_zero_fst ai i \<equiv> if i < length_fst ai then fst ai ! i else 0"
  unfolding get_or_zero_fst_def get_or_zero_def length_fst_def
  by auto

term op_list_get

(*
sepref_thm test is "uncurry (\<lambda> xs i. RETURN (xs ! i))"
  :: "[\<lambda> xs i. i < length xs]\<^sub>f bi_aux_assn\<^sup>k *\<^sub>a (snat_assn' size_t)\<^sup>k \<rightarrow> word_assn' limb\<^sub>w"
  apply sepref_dbg_keep
  apply sepref_dbg_trans_keep
  apply sepref_dbg_trans_step_keep
  apply sepref_dbg_side_unfold
  oops
*)

sepref_def get_or_zero_fst_impl
  is \<open>uncurry (RETURN \<circ>\<circ> get_or_zero_fst)\<close>
  :: \<open>sbi_aux_assn\<^sup>k  *\<^sub>a (snat_assn' TYPE(64))\<^sup>k  \<rightarrow>\<^sub>a word_assn' TYPE(64)\<close>
  unfolding get_or_zero_fst_alt_def length_fst_def[symmetric] 
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_keep
  apply sepref_dbg_trans_keep
  apply sepref_dbg_trans_step_keep
  apply sepref_dbg_side_unfold
  (*fails for the other fst that needs to be fixed with an extra function*)
  apply sepref_dbg_trans
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve_cp
  apply sepref_dbg_constraints
  sorry

text "Reimplement \<le> for signed big integers"
definition signed_big_int_leq_abs :: "signed_big_int \<Rightarrow> signed_big_int \<Rightarrow> bool nres" 
  where "signed_big_int_leq_abs ai bi \<equiv> do {
    let la = length_fst ai;
    let lb = length_fst bi;
    if la = lb 
    then do {
      ASSERT (lb = la);
      if la \<ge> 1 
        then do {
          ASSERT (la \<ge> 1);
          let idx = la - 1;
          idx \<leftarrow> WHILEIT
            (\<lambda> idx . (drop (idx + 1) (fst ai) = drop (idx + 1) (fst bi)))
            \<comment> \<open>TODO: remove dynamic index check\<close> 
            (\<lambda> idx . (get_or_zero_fst ai idx = get_or_zero_fst bi idx) \<and> idx \<ge> 1)
            (\<lambda> idx . do {
              ASSERT (idx \<ge> 1);
              let idx = idx - 1;
              RETURN idx
            }) (idx);
          let aix = get_or_zero_fst ai idx;
          let bix = get_or_zero_fst bi idx;
          let res = aix \<le> bix;
          RETURN res
        }
        else RETURN True 
      }
    else RETURN (la < lb) 
  }"

sepref_def signed_big_int_leq_abs_impl is "uncurry signed_big_int_leq_abs"
  :: "sbi_aux_assn\<^sup>k *\<^sub>a sbi_aux_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding signed_big_int_leq_abs_def
  apply (annot_snat_const size_t)
  by sepref
            
lemma signed_big_int_leq_abs_aux:
  assumes "(aui, au) \<in> big_int_rel"
      and "(bui, bu) \<in> big_int_rel"
      and "(asi, as) \<in> signed_big_int_rel"
      and "(bsi, bs) \<in> signed_big_int_rel"
      and "nat $ abs as = au"
      and "nat $ abs bs = bu"
    shows "signed_big_int_leq_abs asi bsi \<le> big_int_leq aui bui"
proof -
  have rel_a: "(fst asi, au) \<in> big_int_rel"
    using abs_rel[OF assms(3)] assms(5) by (simp add: limbs_of_def)
  have aui_eq: "aui = fst asi"
    using big_int_rel_unique[OF assms(1) rel_a] by simp
  have rel_b: "(fst bsi, bu) \<in> big_int_rel"
    using abs_rel[OF assms(4)] assms(6) by (simp add: limbs_of_def)
  have bui_eq: "bui = fst bsi"
    using big_int_rel_unique[OF assms(2) rel_b] by simp
  have eq: "signed_big_int_leq_abs asi bsi = big_int_leq (fst asi) (fst bsi)"
    unfolding signed_big_int_leq_abs_def big_int_leq_def
              length_fst_def big_int_length_def get_or_zero_fst_def
    by simp
  show ?thesis
    by (simp add: eq aui_eq bui_eq)
qed

lemma signed_big_int_leq_abs_correct:
  assumes "(ai, a) \<in> signed_big_int_rel"
      and "(bi, b) \<in> signed_big_int_rel"
    shows "signed_big_int_leq_abs ai bi \<le> (\<Down> Id) (RETURN (abs a \<le> abs b))"
proof -
  have rel_a: "(fst ai, nat $ abs a) \<in> big_int_rel"
    using abs_rel[OF assms(1)] by (simp add: limbs_of_def)
  have rel_b: "(fst bi, nat $ abs b) \<in> big_int_rel"
    using abs_rel[OF assms(2)] by (simp add: limbs_of_def)
  have step1: "signed_big_int_leq_abs ai bi \<le> big_int_leq (fst ai) (fst bi)"
    using signed_big_int_leq_abs_aux[OF rel_a rel_b assms(1) assms(2) refl refl] .
  have step2: "big_int_leq (fst ai) (fst bi) \<le> (\<Down> Id) (RETURN (nat $ abs a \<le> nat $ abs b))"
    using big_int_leq_correct[OF rel_a rel_b] .
  have nat_abs_eq: "(nat $ abs a \<le> nat $ abs b) = (abs a \<le> abs b)"
    by force
  show ?thesis
    using nat_abs_eq step1 step2 by force
qed

*)

(* end (* of context *) *)
end
