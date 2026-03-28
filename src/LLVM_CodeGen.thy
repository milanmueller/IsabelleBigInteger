theory LLVM_CodeGen
  imports Main "Isabelle_LLVM.IICF" Setup BigInt AuxLemmas Karatsuba BigIntSlice
begin

section \<open>Limb Level Ops\<close>

type_synonym size_t = 64
abbreviation "size_t \<equiv> TYPE(size_t)"
abbreviation "size_assn \<equiv> snat_assn' size_t"

abbreviation "limb\<^sub>w \<equiv> TYPE(limb\<^sub>w)"
abbreviation "limb_assn \<equiv> word_assn' limb\<^sub>w"

abbreviation "double\<^sub>w \<equiv> TYPE(double\<^sub>w)"
abbreviation "double_assn \<equiv> word_assn' double\<^sub>w"


lemma is_upcast: "is_up' UCAST(limb\<^sub>w \<rightarrow> double\<^sub>w)"
  by (auto simp: is_up')

lemma is_downcast: "is_down' UCAST(double\<^sub>w \<rightarrow> limb\<^sub>w)"
  by (auto simp: is_down')

sepref_def add_carry_impl is "uncurry2 (RETURN ooo add_carry)" :: "limb_assn\<^sup>k *\<^sub>a limb_assn\<^sup>k *\<^sub>a limb_assn\<^sup>k \<rightarrow>\<^sub>a limb_assn \<times>\<^sub>a limb_assn"
  unfolding add_carry_def
  by sepref

(*lemma [sepref_import_param]: "(extend,extend)\<in> Id \<rightarrow> Id" by simp*)
(*lemma [sepref_import_param]: "(cutoff,cutoff)\<in> Id \<rightarrow> Id" by simp*)

sepref_register
  extend: extend 
  cutoff: cutoff


context
begin  
  interpretation llvm_prim_arith_setup .

  lemma extend_hnr[sepref_fr_rules]: "(\<lambda>w. ll_zext w TYPE (double\<^sub>w word), RETURN o extend) \<in> limb_assn\<^sup>k \<rightarrow>\<^sub>a double_assn"  
    supply [simp] = is_upcast
    apply sepref_to_hoare
    by vcg

  lemma cutoff_hnr[sepref_fr_rules]: "(\<lambda>w. ll_trunc w TYPE (limb\<^sub>w word), RETURN o cutoff) \<in> double_assn\<^sup>k \<rightarrow>\<^sub>a limb_assn"  
    supply [simp] = is_downcast
    apply sepref_to_hoare
    by vcg

end 

lemma limb_wd_unfold: "limb_wd = 64" 
  unfolding limb_wd_def
  by simp

sepref_def limb_wd_def [llvm_inline] is "uncurry0 (RETURN limb_wd)" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a size_assn"
  unfolding limb_wd_unfold
  apply (annot_snat_const size_t)
  by sepref

sepref_def mul_add_impl is "uncurry2 (RETURN ooo mul_add)" 
  :: "limb_assn\<^sup>k *\<^sub>a limb_assn\<^sup>k *\<^sub>a limb_assn\<^sup>k \<rightarrow>\<^sub>a limb_assn \<times>\<^sub>a limb_assn"
  unfolding mul_add_def
  supply [simp] = is_upcast limb_wd_unfold
  apply (rewrite at "shiftr _ \<hole>" annot_snat_snat_upcast[where 'l="double\<^sub>w"])
  by sepref


section \<open>Basic algorithms on big_int\<close>  
  
abbreviation "bi_aux_assn \<equiv> al_assn' size_t (word_assn' limb\<^sub>w)"

definition "bi_assn \<equiv> hr_comp bi_aux_assn big_int_rel"

lemmas [safe_constraint_rules] = CN_FALSEI[of is_pure bi_assn]



lemma bi_assn_free[sepref_frame_free_rules]: "MK_FREE (bi_assn) arl_free"
  unfolding bi_assn_def by (rule sepref_frame_free_rules)+
  
  
context
  notes [fcomp_norm_unfold] = bi_assn_def[symmetric]
begin
    
sepref_def big_int_length_impl is "RETURN o big_int_length" :: "bi_aux_assn\<^sup>k \<rightarrow>\<^sub>a size_assn"
  unfolding big_int_length_def
  by sepref

lemma big_int_length_refine: "(big_int_length, size_log) \<in> big_int_rel \<rightarrow> nat_rel"  
  using big_int_length_correct by (auto simp: big_int_rel_def in_br_conv)
  
lemmas [sepref_fr_rules] = big_int_length_impl.refine[FCOMP big_int_length_refine]
  

sepref_def big_int0_impl is "uncurry0 (RETURN big_int0)" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a bi_aux_assn"
  unfolding big_int0_def
  apply (rewrite al_fold_custom_empty[where 'l=size_t])
  by sepref

lemma big_int0_refine: "(big_int0, 0) \<in> big_int_rel" by simp

lemmas [sepref_fr_rules] = big_int0_impl.refine[FCOMP big_int0_refine]


sepref_def bi_append_impl [llvm_inline] is "uncurry bi_append" :: "bi_aux_assn\<^sup>d *\<^sub>a limb_assn\<^sup>k \<rightarrow>\<^sub>a bi_aux_assn"
  unfolding bi_append_def
  by sepref

(*lemma bi_append_refine: "(bi_append, mop_list_append) \<in> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  unfolding bi_append_def mop_list_append_def
  by (refine_vcg; simp)

(* Question: Do "internal" operations need these sepref_fr_rules *)
lemmas [sepref_fr_rules] = bi_append_impl.refine[FCOMP bi_append_refine]

*)


sepref_def big_int_trim_impl is big_int_trim :: "bi_aux_assn\<^sup>d \<rightarrow>\<^sub>a bi_aux_assn"
  unfolding big_int_trim_def big_int_last_limb_def big_int_length_def
  apply (annot_snat_const size_t)
  apply (rewrite in "WHILEIT _ \<hole>" short_circuit_conv)
  by sepref

thm "big_int_trim_correct" (* big int trim has no \<open>refinement\<close> lemma *)


sepref_def get_or_zero_impl is "uncurry (RETURN oo get_or_zero)" :: "bi_aux_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a limb_assn"
  unfolding get_or_zero_def by sepref

sepref_def big_int_mult_limb_aux_impl is "uncurry big_int_mult_limb_aux" :: "bi_aux_assn\<^sup>k *\<^sub>a limb_assn\<^sup>k \<rightarrow>\<^sub>a bi_aux_assn"
  unfolding big_int_mult_limb_aux_def 
  apply (annot_snat_const size_t)
  by sepref

sepref_def big_int_mult_limb_impl is "uncurry big_int_mult_limb" :: "bi_aux_assn\<^sup>k *\<^sub>a limb_assn\<^sup>k \<rightarrow>\<^sub>a bi_aux_assn"
  unfolding big_int_mult_limb_def
  by sepref

sepref_def big_int_add_loop_impl is "uncurry2 big_int_add_loop" 
  :: "bi_aux_assn\<^sup>k *\<^sub>a bi_aux_assn\<^sup>k *\<^sub>a limb_assn\<^sup>k \<rightarrow>\<^sub>a bi_aux_assn"
  unfolding big_int_add_loop_def big_int_add_cond_def
  apply (annot_snat_const size_t)
  by sepref

sepref_def big_int_add_impl is "uncurry big_int_add" :: "bi_aux_assn\<^sup>k *\<^sub>a bi_aux_assn\<^sup>k \<rightarrow>\<^sub>a bi_aux_assn"
  unfolding big_int_add_def                 
  by sepref

(* Question: Can we "simply" lift (+) to nres without extra definition *)

lemma big_int_add_refine: "(big_int_add, RETURN oo (+)) \<in> big_int_rel \<rightarrow> big_int_rel \<rightarrow> \<langle>big_int_rel\<rangle>nres_rel" 
  by (auto simp: big_int_add_correct nres_rel_def)

lemmas [sepref_fr_rules] = big_int_add_impl.refine[FCOMP big_int_add_refine]

(*
sepref_definition foo is "uncurry2 (\<lambda>a b c. RETURN (a+b+c))" :: "bi_assn\<^sup>k *\<^sub>a bi_assn\<^sup>k *\<^sub>a bi_assn\<^sup>k \<rightarrow>\<^sub>a bi_assn"
  by sepref
*)

(*
definition add_nat:: "nat \<Rightarrow> nat \<Rightarrow> nat nres" where "add_nat a b \<equiv> RETURN (a+b)" 

lemma big_int_add_refine: "(big_int_add, add_nat) \<in> big_int_rel \<rightarrow> big_int_rel \<rightarrow> \<langle>big_int_rel\<rangle>nres_rel" 
  unfolding add_nat_def
  by (auto simp: big_int_add_correct nres_rel_def)

lemmas [sepref_fr_rules] = big_int_add_impl.refine[FCOMP big_int_add_refine]
*)

sepref_def big_int_add_inc_impl is "uncurry big_int_add_inc" :: "bi_aux_assn\<^sup>k *\<^sub>a bi_aux_assn\<^sup>k \<rightarrow>\<^sub>a bi_aux_assn"
  unfolding big_int_add_inc_def
  by sepref

(* Question: Same as above *)
definition add_inc_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where [simp]: "add_inc_nat a b \<equiv> (a+b+1)"
sepref_register add_inc_nat

lemma big_int_add_inc_refine: "(big_int_add_inc, RETURN oo add_inc_nat) \<in> big_int_rel \<rightarrow> big_int_rel \<rightarrow> \<langle>big_int_rel\<rangle>nres_rel" 
  unfolding add_inc_nat_def
  using big_int_add_inc_correct nres_rel_def 
  by fastforce

lemmas [sepref_fr_rules] = big_int_add_inc_impl.refine[FCOMP big_int_add_inc_refine]


sepref_def big_int_take_impl is "uncurry big_int_take" :: "size_assn\<^sup>k *\<^sub>a bi_aux_assn\<^sup>d \<rightarrow>\<^sub>a bi_aux_assn"
  unfolding big_int_take_def                   
  by sepref

(* TODO: maybe do this in-place *)
sepref_def big_int_compl_impl is "uncurry big_int_compl" :: "bi_aux_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a bi_aux_assn"
  unfolding big_int_compl_def compl_def compl_cond_def
  apply (annot_snat_const size_t)
  by sepref

sepref_def big_int_sub_compl_impl is "uncurry big_int_sub_compl" :: "bi_aux_assn\<^sup>k *\<^sub>a bi_aux_assn\<^sup>k \<rightarrow>\<^sub>a bi_aux_assn"
  unfolding big_int_sub_compl_def
  by sepref

sepref_def big_int_eq_impl is "uncurry big_int_eq" :: "bi_aux_assn\<^sup>k *\<^sub>a bi_aux_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding big_int_eq_def
  apply (annot_snat_const size_t)
  by sepref

sepref_def big_int_fits_limb_impl is "RETURN o big_int_fits_limb" :: "bi_aux_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding big_int_fits_limb_def
  apply (annot_snat_const size_t)
  by sepref

sepref_def big_int_leq_impl is "uncurry big_int_leq" :: "bi_aux_assn\<^sup>k *\<^sub>a bi_aux_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding big_int_leq_def big_int_length_def
  apply (annot_snat_const size_t)
  by sepref
  (* NOTE: Assert part of loop invariant or condition when relevant for execution *)

sepref_def big_int_gt_impl is "uncurry big_int_gt" :: "bi_aux_assn\<^sup>k *\<^sub>a bi_aux_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding big_int_gt_def
  by sepref

sepref_def big_int_geq_impl is "uncurry big_int_geq" :: "bi_aux_assn\<^sup>k *\<^sub>a bi_aux_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding big_int_geq_def
  by sepref

sepref_def big_int_lt_impl is "uncurry big_int_lt" :: "bi_aux_assn\<^sup>k *\<^sub>a bi_aux_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding big_int_lt_def
  by sepref

  

definition "pad0 n xs \<equiv> doN {
  ASSUME (sepref_sorry_that(n + length xs < max_snat LENGTH(size_t)));
  let rs = replicate (n + length xs) (0::limb);
  rs \<leftarrow> forI 
    (\<lambda>i rs. rs = replicate n 0 @ take i xs @ replicate (length xs - i) 0) 
    0 (length xs) (\<lambda>i rs. doN { x\<leftarrow>mop_list_get xs i; ASSERT(i+n < max_snat LENGTH(size_t)); mop_list_set rs (i+n) x } ) rs;
  mop_free xs;  
  RETURN rs  
}"
    
lemma pad0_correct[refine_vcg]: "pad0 n xs \<le> SPEC (\<lambda>r. r = replicate n 0 @ xs)"
  unfolding pad0_def mop_free_def
  apply refine_vcg
  apply (clarsimp_all simp: replicate_add list_update_append)
  subgoal for i by (cases "length xs - i"; simp add: take_Suc_conv_app_nth)
  done
  
sepref_def pad0_impl is "uncurry pad0" :: "size_assn\<^sup>k *\<^sub>a (al_assn' TYPE(size_t) id_assn)\<^sup>d \<rightarrow>\<^sub>a al_assn' TYPE(size_t) id_assn"  
  unfolding pad0_def
  apply (rewrite al_fold_custom_replicate)
  apply (annot_snat_const size_t)
  
  apply (rewrite forI_as_for)
  apply (rewrite for_by_while[where 'l=size_t])
  by sepref
  
definition big_int_rshift2 :: "nat \<Rightarrow> big_int \<Rightarrow> big_int nres"
  where "big_int_rshift2 m ai \<equiv> doN { xs \<leftarrow> pad0 m ai; big_int_trim xs }"
  
lemma big_int_rshift2_refine: "(big_int_rshift2, big_int_rshift) \<in> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  unfolding big_int_rshift2_def big_int_rshift_def
  apply (refine_vcg specify_left[of "pad0 _ _"])
  by auto
  
sepref_register pad0 big_int_trim  
  
sepref_def big_int_rshift2_impl is "uncurry big_int_rshift2" :: "size_assn\<^sup>k *\<^sub>a bi_aux_assn\<^sup>d \<rightarrow>\<^sub>a bi_aux_assn"
  unfolding big_int_rshift2_def
  by sepref

lemmas [sepref_fr_rules] = big_int_rshift2_impl.refine[FCOMP big_int_rshift2_refine]
  
section \<open>Algorithms on big-int-slice\<close>  

term big_int_slice_trim
term bis_assn
term larray_free

abbreviation "bi_slice_assn \<equiv> bis_assn' size_t :: (limb list \<times> _) \<Rightarrow> _"

(* HERE *)
definition bi_slice_free1 :: "BI_s \<Rightarrow> unit" where "bi_slice_free1 nxs \<equiv> case nxs of (xs,_) \<Rightarrow> op_list_free xs"
lemma bi_slice_free1_refine: "(bi_slice_free1,op_list_free) \<in> bis_rel \<rightarrow> unit_rel" by auto

term "la_free1"
sepref_definition la_free_impl [llvm_inline] is "RETURN o bi_slice_free1" :: "(bi_slice_assn)\<^sup>d \<rightarrow>\<^sub>a unit_assn"
  unfolding bi_slice_free1_def bis_assn_def
  apply sepref_dbg_keep
  oops

sepref_decl_impl larray_free: la_free_impl.refine[FCOMP la_free1_refine] .
lemmas larray_mk_free[sepref_frame_free_rules] = hn_MK_FREEI[OF larray_free_hnr]
  

find_theorems "MK_FREE (_ \<times>\<^sub>a _)"

lemma "MK_FREE bis_assn (\<lambda>(c\<^sub>1, c\<^sub>2). do\<^sub>M {
           (\<lambda>_. Mreturn ()) c\<^sub>1;
           (\<lambda>_. Mreturn ()) c\<^sub>2
         })"
  unfolding bis_assn_def 
  apply (rule mk_free_pair)
  oops

sepref_def big_int_slice_trim_done_impl is big_int_slice_trim_done :: "bi_slice_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding big_int_slice_trim_done_def                                   
  apply (annot_snat_const size_t)
  by sepref

sepref_def big_int_slice_trim_impl is big_int_slice_trim :: "bi_slice_assn\<^sup>d \<rightarrow>\<^sub>a bi_slice_assn"
  unfolding big_int_slice_trim_def
  by sepref

sepref_def bis_get_or_zero_impl is "uncurry bis_get_or_zero" :: "bi_slice_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a limb_assn"
  unfolding bis_get_or_zero_def
  by sepref

sepref_def big_int_slice_add_loop_impl is "uncurry big_int_slice_add_loop" 
  :: "bi_slice_assn\<^sup>k *\<^sub>a bi_slice_assn\<^sup>k \<rightarrow>\<^sub>a bi_aux_assn"
  unfolding big_int_slice_add_loop_def
  apply (annot_snat_const size_t)
  by sepref

sepref_def big_int_slice_add_impl is "uncurry big_int_slice_add" 
  :: "bi_slice_assn\<^sup>k *\<^sub>a bi_slice_assn\<^sup>k \<rightarrow>\<^sub>a bi_aux_assn"
  unfolding big_int_slice_add_def
  by sepref

sepref_def big_int_mult_limb_slice_impl is "uncurry big_int_mult_limb_slice"
  :: "bi_slice_assn\<^sup>k *\<^sub>a limb_assn\<^sup>k \<rightarrow>\<^sub>a bi_aux_assn"
  unfolding big_int_mult_limb_slice_def big_int_mult_limb_slice_aux_def
  apply (annot_snat_const limb\<^sub>w)
  by sepref

sepref_def big_int_mult_limb_slice_small_impl is "uncurry big_int_mult_limb_slice_small"
  :: "bi_slice_assn\<^sup>k *\<^sub>a bi_slice_assn\<^sup>k \<rightarrow>\<^sub>a bi_aux_assn"
  unfolding big_int_mult_limb_slice_small_def bis_get_def
  by sepref

term "bi_aux_assn"
term "bi_slice_assn"

find_theorems "Pair" name: "sepref"

(* Array to Slice transformation *)

sepref_register mop_bis_make mop_bis_unmake

sepref_def bis_make_impl is "mop_bis_make" :: "
  [\<lambda>_. True]\<^sub>c bi_aux_assn\<^sup>d \<rightarrow> bi_slice_assn \<times>\<^sub>a al_slice_diff_assn' TYPE(64) TYPE(64 word) 
    [\<lambda>(l,c,p) ((p',_),(l'',c'',p'')). p'=p \<and> p''=p \<and> l''=l \<and> c''=c]\<^sub>c"
  unfolding mop_bis_make_def bis_assn_def
  by sepref

sepref_def bis_unmake_impl is "uncurry mop_bis_unmake" :: "
  [\<lambda>(p1,al). CP_cond (fst p1=snd (snd al))]\<^sub>c 
    bi_slice_assn\<^sup>d *\<^sub>a (al_slice_diff_assn' TYPE(64) TYPE(64 word))\<^sup>d \<rightarrow> bi_aux_assn
  [\<lambda>(_,(l,c,p)) (l',c',p'). l'=l \<and> c'=c \<and> p'=p]\<^sub>c"
  unfolding mop_bis_unmake_def bis_assn_def
  by sepref


definition op_min_div2 :: "nat \<Rightarrow> nat \<Rightarrow> nat" where "op_min_div2 a b \<equiv> min a b div 2"
  
sepref_def min_div2_impl [llvm_inline] is "uncurry (RETURN oo op_min_div2)" :: "size_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a size_assn"
  unfolding op_min_div2_def 
  apply (annot_snat_const size_t)
  by sepref

definition karatsuba_body_tail where "karatsuba_body_tail z_2 z_0 z_p m \<equiv> doN {
  z_sum \<leftarrow> big_int_add z_2 z_0;

  z_1 \<leftarrow> big_int_sub_compl z_p z_sum;

  z_1 \<leftarrow> big_int_rshift m z_1;

  aux \<leftarrow> big_int_add z_1 z_0;
  ASSERT (2 * m < max_snat (len_of limb\<^sub>w)); \<comment> \<open>TODO: this should be length of ai or bi\<close>
  let m2 = 2 * m;
  z_2 \<leftarrow> big_int_rshift m2 z_2;

  res \<leftarrow> big_int_add aux z_2;

  RETURN res
}"

term karatsuba_body_tail
term "uncurry3 karatsuba_body_tail"

sepref_def karatsuba_body_tail_impl[llvm_inline] is "uncurry3 karatsuba_body_tail" :: "bi_aux_assn\<^sup>d *\<^sub>a bi_aux_assn\<^sup>k *\<^sub>a bi_aux_assn\<^sup>k *\<^sub>a size_assn\<^sup>k \<rightarrow>\<^sub>a bi_aux_assn"
  unfolding karatsuba_body_tail_def
  apply (annot_snat_const size_t)
  by sepref

definition karatsuba_body_prelude where "karatsuba_body_prelude ais_r ais_l bis_r bis_l \<equiv> doN {
  ais_r \<leftarrow> big_int_slice_trim ais_r;
  ais_l \<leftarrow> big_int_slice_trim ais_l;
  bis_r \<leftarrow> big_int_slice_trim bis_r;
  bis_l \<leftarrow> big_int_slice_trim bis_l;
  ai_sum \<leftarrow> big_int_slice_add ais_l ais_r;
  bi_sum \<leftarrow> big_int_slice_add bis_l bis_r;
  RETURN (ais_r, ais_l, bis_r, bis_l, ai_sum, bi_sum)
}"

term karatsuba_body_prelude

sepref_def karatsuba_body_prelude_impl[llvm_inline] is "uncurry3 karatsuba_body_prelude" 
  :: "bi_slice_assn\<^sup>d *\<^sub>a bi_slice_assn\<^sup>d *\<^sub>a bi_slice_assn\<^sup>d *\<^sub>a bi_slice_assn\<^sup>d \<rightarrow>\<^sub>a bi_slice_assn \<times>\<^sub>a bi_slice_assn \<times>\<^sub>a bi_slice_assn \<times>\<^sub>a bi_slice_assn \<times>\<^sub>a bi_aux_assn \<times>\<^sub>a bi_aux_assn"
  unfolding karatsuba_body_prelude_def
  by sepref

definition karatsuba_slice' :: "BI_s \<Rightarrow> BI_s \<Rightarrow> big_int nres"
  where "karatsuba_slice' ais bis \<equiv> do {
    (RECT (\<lambda> kara (ais, bis). do {
      if bis_len ais = 0 then RETURN big_int0 else
      if bis_len bis = 0 then RETURN big_int0 else
      if bis_len ais = 1 then big_int_mult_limb_slice_small ais bis else
      if bis_len bis = 1 then big_int_mult_limb_slice_small bis ais else
      do {
        let la = bis_len ais;
        let lb = bis_len bis;
        ASSERT (la \<ge> 2);
        ASSERT (lb \<ge> 2);

        let m = op_min_div2 la lb;
        
        WITH_SPLIT_bis_ro m ais (\<lambda> ais_r ais_l. do {
          WITH_SPLIT_bis_ro m bis (\<lambda> bis_r bis_l. do {

            (ais_r, ais_l, bis_r, bis_l, ai_sum, bi_sum) \<leftarrow> karatsuba_body_prelude ais_r ais_l bis_r bis_l;

            (ai_sum,taga) \<leftarrow> mop_bis_make ai_sum;
            (bi_sum,tagb) \<leftarrow> mop_bis_make bi_sum;

            z_2 \<leftarrow> kara (ais_l, bis_l);
            z_0 \<leftarrow> kara (ais_r, bis_r);
            z_p \<leftarrow> kara (ai_sum, bi_sum);

            ai_sum \<leftarrow> mop_bis_unmake ai_sum taga;
            bi_sum \<leftarrow> mop_bis_unmake bi_sum tagb;

            karatsuba_body_tail z_2 z_0 z_p m
          })
        })
      }
    })) (ais, bis)
  }"

thm  hn_RECT'[where Rx'="bi_slice_assn \<times>\<^sub>a bi_slice_assn"]
  (* supply [sepref_comb_rules] = hn_RECT'[where Rx'="bi_slice_assn \<times>\<^sub>a bi_slice_assn"] *)
  
find_theorems WITH_SPLIT_ro
  
find_in_thms bis_assn in sepref_fr_rules
thm "RECT_cp_annot"

sepref_register bis_constr bis_destr

sepref_def bis_constr_impl [llvm_inline] is "uncurry (RETURN oo bis_constr)" 
  :: "[\<lambda>_. True]\<^sub>c (array_slice_assn id_assn)\<^sup>d *\<^sub>a (snat_assn' TYPE('l::len2))\<^sup>k \<rightarrow> bis_assn' TYPE('l) [\<lambda>(p,l) (p',l'). p'=p \<and> l'=l ]\<^sub>c"
  unfolding bis_constr_def bis_assn_def apply sepref done

sepref_def bis_destr_impl [llvm_inline] is "RETURN o bis_destr" 
  :: "[\<lambda>_. True]\<^sub>c (bis_assn' TYPE('l))\<^sup>d \<rightarrow> (array_slice_assn id_assn \<times>\<^sub>a snat_assn' TYPE('l::len2)) [\<lambda>(p,l) (p',l'). p'=p \<and> l'=l ]\<^sub>c"
  unfolding bis_destr_def bis_assn_def apply sepref done
  
sepref_def karatsuba_slice_impl is "uncurry karatsuba_slice'" :: 
  "bi_slice_assn\<^sup>k *\<^sub>a bi_slice_assn\<^sup>k \<rightarrow>\<^sub>a bi_aux_assn"
  unfolding karatsuba_slice'_def WITH_SPLIT_bis_ro_def
  apply (annot_snat_const size_t)
  supply [sepref_comb_rules] = hn_RECT'[where Rx'="bi_slice_assn \<times>\<^sub>a bi_slice_assn"]
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans_keep

  apply (sepref_dbg_trans_step; succeed)+
  apply sepref_dbg_trans_step
  apply (sepref_dbg_trans_step; succeed)+
  apply sepref_dbg_trans_step
  apply (sepref_dbg_trans_step; succeed)+
  apply sepref_dbg_trans_step
  apply (sepref_dbg_trans_step; succeed)+
  apply sepref_dbg_trans_step
  apply (sepref_dbg_trans_step; succeed)+
  apply sepref_dbg_trans_step
  apply (sepref_dbg_trans_step; succeed)+
  apply sepref_dbg_trans_step
  apply (sepref_dbg_trans_step; succeed)+
  apply -
  apply sepref_dbg_trans_step_keep
  oops
  apply -
  apply (sepref_dbg_trans_step; succeed)+
  apply sepref_dbg_trans_step
  apply (sepref_dbg_trans_step; succeed)+
  apply sepref_dbg_trans_step
  apply (sepref_dbg_trans_step; succeed)+
  apply sepref_dbg_trans_step
  apply (sepref_dbg_trans_step; succeed)+
  apply sepref_dbg_trans_step
  apply (sepref_dbg_trans_step; succeed)+
  apply sepref_dbg_trans_step
  subgoal
  apply (thin_tac "CP_assm _")+
  apply sepref_dbg_side_keep
  apply sepref_dbg_side_bounds
  
  oops
  apply (repeat 100 sepref_dbg_trans_step)
  apply (repeat 500 \<open>sepref_dbg_trans_step; succeed\<close>)
  apply (repeat 100 \<open>tactic \<open>tracing "x";all_tac\<close>; sepref_dbg_trans_step\<close>)
  
  
  find_in_thms RECT in sepref_comb_rules
  
  oops
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply (repeat 100 sepref_dbg_trans_step)
  apply sepref_dbg_trans_step
  apply -
  supply [[linarith_split_limit=15]]
  apply (simp add: bind_ref_tag_def) 
  apply -
  apply (thin_tac "CP_assm _")+
  
  
  oops
  apply sepref_dbg_keep
  apply sepref_dbg_trans_keep
  apply sepref_dbg_trans_step_keep
apply -
oops end end end
sepref_def karatsuba_slice_impl is "uncurry karatsuba_slice'" :: 
  "bi_slice_assn\<^sup>k *\<^sub>a bi_slice_assn\<^sup>k \<rightarrow>\<^sub>a bi_aux_assn"
  unfolding karatsuba_slice'_def WITH_SPLIT_bis_ro_def WITH_SPLIT_ro_def
  apply (annot_snat_const size_t)
  apply sepref_dbg_keep
  apply sepref_dbg_trans_keep
  apply sepref_dbg_trans_step_keep
  (* HERE *)
  oops

section \<open>Old code\<close>

definition "bi_assn \<equiv> hr_comp bi_aux_assn big_int_rel"
lemmas [fcomp_norm_unfold] = bi_assn_def[symmetric]
  
lemmas big_int_plus_hnr[sepref_fr_rules] = big_int_add_impl.refine[FCOMP big_int_add_correct]

definition [llvm_code]: "big_int_add_impl' rlp alp blp \<equiv> doM {
  al \<leftarrow> ll_load alp;
  bl \<leftarrow> ll_load blp;
  rl \<leftarrow> big_int_add_impl al bl;
  ll_store rl rlp
}"

context
begin

  interpretation llvm_prim_mem_setup .

  theorem big_int_add_impl'_htriple: "llvm_htriple 
    (   \<upharpoonleft>ll_pto rlXX rlp 
     ** \<upharpoonleft>ll_pto al alp ** bi_assn a al
     ** \<upharpoonleft>ll_pto bl blp ** bi_assn b bl
    )
    (big_int_add_impl' rlp alp blp)
    (\<lambda>_::unit. EXS rl.
     \<upharpoonleft>ll_pto rl rlp ** bi_assn (a+b) rl
     ** \<upharpoonleft>ll_pto al alp ** bi_assn a al
     ** \<upharpoonleft>ll_pto bl blp ** bi_assn b bl    
    )"
    unfolding big_int_add_impl'_def
    supply [vcg_rules] = big_int_plus_hnr[to_hnr, THEN hn_refineD, unfolded hn_ctxt_def, simplified]
    by vcg

end

  
export_llvm foo: big_int_add_impl' is "void big_int_trim(bigint_t*, bigint_t*, bigint_t*)"
  defines \<open>
    typedef uint64_t limb_t;
    typedef struct {
      int64_t len;
      struct {
        int64_t cap;
        limb_t *data;
      };
    } bigint_t;
  \<close>





(*
sepref_def karatsuba_slice_impl is "uncurry karatsuba_slice"
  :: "bi_slice_assn\<^sup>k *\<^sub>a bi_slice_assn\<^sup>k \<rightarrow>\<^sub>a bi_aux_assn"
  unfolding karatsuba_slice_def
  apply (annot_snat_const size_t)
  apply (sepref_dbg_keep)
  apply (sepref_dbg_trans_keep)
  apply (sepref_dbg_trans_step_keep)
  apply (sepref_dbg_trans_step_keep)
  


term pure_part  
  
find_theorems al_assn length
thm al_assn_boundD (* Check there for proof. And declare as [sepref_bounds_dest] *)
  




sepref_def big_int_small_to_limb_impl is "big_int_small_to_limb" :: "bi_aux_assn\<^sup>k \<rightarrow>\<^sub>a limb_assn"
  unfolding big_int_small_to_limb_def op_list_hd_def
  apply sepref_dbg_keep
  apply sepref_dbg_trans_keep

  
  

sepref_def karatsuba_slow_impl is "uncurry karatsuba" :: "bi_aux_assn\<^sup>k *\<^sub>a bi_aux_assn\<^sup>k \<rightarrow>\<^sub>a bi_aux_assn"
  unfolding karatsuba_def
  apply (annot_snat_const size_t)
  apply sepref_dbg_keep
  apply sepref_dbg_trans_keep

lemma karatsuba_correct': "(karatsuba, RETURN oo (*)) \<in> big_int_rel \<rightarrow> big_int_rel \<rightarrow> \<langle>big_int_rel\<rangle>nres_rel"
  using karatsuba_correct
  by (auto intro: nres_relI)

*)


end