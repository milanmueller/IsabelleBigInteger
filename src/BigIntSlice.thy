theory BigIntSlice 
  imports "Karatsuba" "IICF_More_Array" "HOL-Library.More_List"
begin

type_synonym 'a bis = "('a list \<times> nat)" 
 
definition bis_\<alpha> :: "'a bis \<Rightarrow> 'a list" where "bis_\<alpha> \<equiv> \<lambda>(xs,n). take n xs"
definition bis_invar :: "'a bis \<Rightarrow> bool" where "bis_invar \<equiv> \<lambda>(xs,n). n \<le> length xs"
definition bis_rel :: "('a bis \<times> 'a list) set" where "bis_rel \<equiv> br bis_\<alpha> bis_invar"

definition bis_len :: "'a bis \<Rightarrow> nat" where "bis_len \<equiv> snd"
definition bis_get :: "'a bis \<Rightarrow> nat \<Rightarrow> 'a nres" where "bis_get \<equiv> \<lambda>(xs,_) i. mop_list_get xs i" (* Q: this accesses beyond bis_len *)
definition bis_pop :: "'a bis \<Rightarrow> 'a bis nres" where "bis_pop \<equiv> \<lambda>(xs,n). do { 
  ASSERT (n>0);
  let new_n = n - 1;
  RETURN (xs,new_n)
}"


definition bis_last :: "'a bis \<Rightarrow> 'a nres" where "bis_last \<equiv> \<lambda>sl. do { 
  let l = bis_len sl;
  ASSERT (l > 0);
  let last_idx = l - 1;
  last_limb \<leftarrow> bis_get sl last_idx;
  RETURN last_limb 
}"

lemma bis_len_refine: "(bis_len,op_list_length) \<in> bis_rel \<rightarrow> nat_rel"
  by (auto simp: bis_rel_def bis_invar_def in_br_conv bis_len_def bis_\<alpha>_def)

lemma bis_get_refine: "(bis_get,mop_list_get) \<in> bis_rel \<rightarrow> nat_rel \<rightarrow> \<langle>Id\<rangle>nres_rel"
  by (auto simp: bis_rel_def bis_invar_def in_br_conv bis_get_def bis_\<alpha>_def fun_eq_iff pw_nres_rel_iff refine_pw_simps)

thm bis_get_refine[param_fo, THEN nres_relD]
thm bis_len_refine[param_fo]

find_theorems "nth" "hd"

lemma bis_len_unfold: "(ais, ai) \<in> bis_rel \<Longrightarrow> bis_len ais = length ai" using bis_len_refine[param_fo] by fastforce

lemma mop_list_get_last: "mop_list_get xs (op_list_length xs - 1) \<le> (\<Down> Id) (mop_list_last xs)"
  unfolding mop_list_get_alt mop_list_last_alt pre_list_get_def op_list_length_def op_list_get_def op_list_last_def
  apply (refine_vcg)
  using last_conv_nth 
  by force+

lemma bis_last_refine: "(bis_last, mop_list_last) \<in> bis_rel \<rightarrow> \<langle>Id\<rangle>nres_rel"
  unfolding bis_last_def mop_list_last_def pre_list_last_def mop_def bis_rel_def bis_len_def
  apply (refine_rcg)
  apply (simp add: in_br_conv bis_invar_def bis_\<alpha>_def)
  apply force
  apply (clarsimp simp: in_br_conv bis_invar_def bis_\<alpha>_def bis_get_def last_take_nth_conv)
  apply (refine_vcg)
  apply linarith
  apply simp
  done

thm bis_last_refine[param_fo]
  
lemma bis_pop_refine: "(bis,xs)\<in>bis_rel \<Longrightarrow> xs\<noteq>[] \<Longrightarrow> bis_pop bis \<le> \<Down>bis_rel (mop_list_butlast xs)"
  unfolding bis_pop_def
  apply (refine_vcg)
  apply (auto simp: bis_rel_def bis_invar_def in_br_conv bis_get_def bis_\<alpha>_def butlast_take)
  done
  
definition bis_assn :: "'a::llvm_rep list \<times> nat \<Rightarrow> 'a ptr \<times> 'l::len2 word \<Rightarrow> assn" where "bis_assn \<equiv> array_slice_assn id_assn \<times>\<^sub>a snat_assn' TYPE('l)"
abbreviation bis_assn' :: "'l::len2 itself \<Rightarrow> 'a::llvm_rep list \<times> nat \<Rightarrow> 'a ptr \<times> 'l word \<Rightarrow> assn"  where "bis_assn' TYPE('l) \<equiv> bis_assn"

(* Array slice assn is not pure *)
thm CN_FALSEI[of is_pure "array_slice_assn A" for A]

sepref_def bis_len_impl is "RETURN o bis_len" :: "(bis_assn' TYPE('l::len2))\<^sup>k \<rightarrow>\<^sub>a snat_assn' TYPE('l)"
  unfolding bis_len_def bis_assn_def snd_def
  by sepref
 
sepref_def bis_get_impl is "uncurry bis_get" 
  :: "(bis_assn' TYPE('l::len2))\<^sup>k *\<^sub>a (snat_assn' TYPE('l))\<^sup>k  \<rightarrow>\<^sub>a id_assn"
  unfolding bis_get_def bis_assn_def snd_def bis_len_def
  by sepref

sepref_def bis_pop_impl is "bis_pop"
  :: "(bis_assn' TYPE('l::len2))\<^sup>d \<rightarrow>\<^sub>a bis_assn' TYPE('l::len2)"
  unfolding bis_pop_def bis_assn_def snd_def bis_len_def
  apply (annot_snat_const "TYPE('l)")
  by sepref
  (* NOTE: when using tuple destructuring need to unfold *)

sepref_def bis_last_impl is "bis_last"
  :: "(bis_assn' TYPE('l::len2))\<^sup>k \<rightarrow>\<^sub>a id_assn"
  unfolding bis_last_def bis_len_def bis_get_def bis_assn_def snd_def bis_assn_def snd_def
  apply (annot_snat_const "TYPE('l)")
  by (sepref_dbg_keep)
  (* NOTE: when stuck in sepref, try to decompose the original function into multiple steps *)


(*  
definition "bis_assn A \<equiv> hr_comp bis_raw_assn (\<langle>the_pure A\<rangle>list_rel \<times>\<^sub>r Id)"  
  
lemma bis_len_param[param]: "(bis_len,bis_len) \<in> (\<langle>A\<rangle>list_rel \<times>\<^sub>r nat_rel) \<rightarrow> nat_rel"
  unfolding bis_len_def apply parametricity .

(*  
sepref_decl_op (no_def) bis_len :: "(\<langle>A\<rangle>list_rel \<times>\<^sub>r nat_rel) \<rightarrow> nat_rel" .
print_theorems

sepref_decl_op bis_get :: "[\<lambda>(l,i). i<length (fst l)]\<^sub>f (\<langle>A\<rangle>list_rel \<times>\<^sub>r nat_rel) \<times>\<^sub>r nat_rel \<rightarrow> A"
print_theorems
*)

lemma bis_len_fref[to_fref]: "(RETURN o bis_len,RETURN o bis_len)\<in> Id \<rightarrow> \<langle>Id\<rangle>nres_rel" 
  by (auto intro: nres_relI)

lemma bis_get_fref[to_fref]: "(RETURN oo bis_get,RETURN oo bis_get)\<in> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel" 
  by (auto intro: nres_relI)

sepref_decl_op bis_len :: "\<langle>Id\<rangle>list_rel\<times>\<^sub>rnat_rel \<rightarrow> Id"
  
context
  notes [fcomp_norm_unfold] = bis_assn_def[symmetric]
begin  
  
  sepref_decl_impl bis_len_impl.refine uses bis_len_fref .
  sepref_decl_impl bis_get_impl.refine uses bis_get_fref
  
end   
 
*)

lemmas [sepref_comb_rules del] = hn_WITH_SPLIT_woarray_slice

definition "al_slice_diff_assn \<equiv> \<lambda>n (l::'l::len2 word,c::'l word,p). (EXS rest. 
      raw_array_slice_assn rest (p +\<^sub>a int n) 
    ** \<upharpoonleft>array_base_assn (n + length rest) p
    ** \<upharpoonleft>snat.assn (n) l
    ** \<upharpoonleft>snat.assn (n + length rest) c
    ** \<up>(4 < LENGTH('l))
    )"

abbreviation al_slice_diff_assn' :: "'l::len2 itself \<Rightarrow> 'a::llvm_rep itself \<Rightarrow> nat \<Rightarrow> 'l word \<times> 'l word \<times> 'a ptr \<Rightarrow> llvm_amemory \<Rightarrow> bool" 
  where "al_slice_diff_assn' _ _ \<equiv> al_slice_diff_assn"    
    
    
lemma al_slice_conv: "al_assn A xs = (\<lambda>(l::'l::len2 word,c,p). 
    array_slice_assn A xs p 
  ** al_slice_diff_assn (length xs) (l,c,p)
)" 
  unfolding al_slice_diff_assn_def pure_woarray_slice_assn_conv
  unfolding arl_assn_def al_assn_def arl_assn'_def hr_comp_def
     array_assn_split IICF_Array.array_slice_assn_def
  apply clarsimp   
  apply (auto simp: fun_eq_iff sep_algebra_simps)

  subgoal for l c p s n xs'
    apply (simp add: array_slice_assn_split[of "take n xs'" "drop n xs'", simplified])
    apply (rule exI[where x="take n xs'"]; simp)
    apply (rule exI[where x="drop n xs'"])
    apply (auto dest!: list_rel_imp_same_length simp: snat.assn_def sep_algebra_simps) 
    done
    
  subgoal for l c p s xsi rest 
    apply (rule exI[where x=xsi]; simp)
    apply (rule exI[where x="length xs + length rest"])
    apply (rule exI[where x="length xs"]; simp)
    apply (rule exI[where x="xsi@rest"]; simp)
    apply (simp add: array_slice_assn_split)
    apply (auto dest!: list_rel_imp_same_length simp: snat.assn_def sep_algebra_simps) 
    done
  done


(* Converting narray into slice, and back *)
definition "mop_al_split xs = RETURN (xs,length xs)"  
definition [llvm_inline]: "al_split_impl \<equiv> \<lambda>(l,c,p). Mreturn (p,(l,c,p))"

definition "mop_al_combine xs tag = doN {ASSERT (length xs = tag); RETURN xs}"  
definition [llvm_inline]: "al_combine_impl \<equiv> \<lambda>p (l,c,p'). Mreturn (l,c,p)"

  
sepref_register mop_al_split mop_al_combine
  
lemma al_split_hnr[sepref_fr_rules]: 
  "(al_split_impl, mop_al_split) \<in> [\<lambda>_. True]\<^sub>c (al_assn A)\<^sup>d \<rightarrow> array_slice_assn A \<times>\<^sub>a al_slice_diff_assn [\<lambda>(l,c,p) (p',(l'',c'',p'')). p'=p \<and> p''=p \<and> l''=l \<and> c''=c]\<^sub>c"
  apply sepref_to_hoare
  unfolding mop_al_split_def al_split_impl_def al_slice_conv
  by vcg'
  
lemma al_combine_hnr[sepref_fr_rules]:
  "(uncurry al_combine_impl, uncurry mop_al_combine) 
    \<in> [\<lambda>(p1,al). CP_cond (p1=snd (snd al))]\<^sub>c (array_slice_assn A)\<^sup>d *\<^sub>a (al_slice_diff_assn)\<^sup>d \<rightarrow> al_assn A [\<lambda>(_,(l,c,p)) (l',c',p'). l'=l \<and> c'=c \<and> p'=p]\<^sub>c"  
  apply sepref_to_hoare
  unfolding mop_al_combine_def al_combine_impl_def CP_cond_def
  apply (subst al_slice_conv; simp)
  apply (clarsimp simp: refine_pw_simps invalid_assn_def)
  apply vcg'
  done

        

experiment
begin

  definition "test_split_combine_array xs \<equiv> doN {
    (xs,tag) \<leftarrow> mop_al_split xs;
    
    (_,xs) \<leftarrow> WITH_SPLIT 2 xs (\<lambda>xs\<^sub>1 xs\<^sub>2. do {
      xs\<^sub>1 \<leftarrow> mop_list_set xs\<^sub>1 1 True;    
      xs\<^sub>2 \<leftarrow> mop_list_set xs\<^sub>2 1 True;
      RETURN ((),xs\<^sub>1,xs\<^sub>2)
    });
    
    xs \<leftarrow> mop_al_combine xs tag;
  
    RETURN xs
  }"

  
  sepref_def test_split_combine_array_impl is test_split_combine_array :: "(al_assn' TYPE(64) bool1_assn)\<^sup>d \<rightarrow>\<^sub>a al_assn' TYPE(64) bool1_assn"
    unfolding test_split_combine_array_def
    apply (annot_snat_const "TYPE(64)")
    by sepref

    
  definition "test_split_combine_array2 xs \<equiv> doN {
    (xs,tag) \<leftarrow> mop_al_split xs;
    
    r \<leftarrow> WITH_SPLIT_ro 2 xs (\<lambda>xs\<^sub>1 xs\<^sub>2. do {
      x \<leftarrow> mop_list_get xs\<^sub>1 1;    
      y \<leftarrow> mop_list_get xs\<^sub>2 1;
      RETURN (x\<and>y)
    });
    
    xs \<leftarrow> mop_al_combine xs tag;
  
    RETURN (r,xs)
  }"

  
  sepref_def test_split_combine_array2_impl is test_split_combine_array2 :: "(al_assn' TYPE(64) bool1_assn)\<^sup>d \<rightarrow>\<^sub>a bool1_assn \<times>\<^sub>a al_assn' TYPE(64) bool1_assn"
    unfolding test_split_combine_array2_def
    apply (annot_snat_const "TYPE(64)")
    apply sepref_dbg_keep
    done
    
end





(*definition bis_make :: "'a list \<Rightarrow> 'a bis" where "bis_make xs = (xs, length xs)"
lemma bis_make_refine: "(bis_make ai, ai) \<in> bis_rel"
  unfolding bis_make_def bis_rel_def in_br_conv bis_\<alpha>_def bis_invar_def by simp
*)

lemma bis_make_refine: "(xs,xs')\<in>Id \<Longrightarrow> ((xs,length xs),xs')\<in>bis_rel"
  unfolding bis_rel_def in_br_conv bis_\<alpha>_def bis_invar_def by simp

definition mop_bis_make :: "'a list \<Rightarrow> ('a bis \<times> nat) nres" where "mop_bis_make xs = do {
  l \<leftarrow> mop_list_length xs;
  (xs,tag) \<leftarrow> mop_al_split xs;
  RETURN ((xs,l),tag)}"

lemma mop_bis_make_correct[refine_vcg]: "mop_bis_make xs \<le> SPEC (\<lambda>(bis,tag). (bis,xs)\<in>bis_rel \<and> tag = length xs)"  
  unfolding mop_bis_make_def mop_al_split_def
  apply refine_vcg
  unfolding bis_rel_def in_br_conv bis_\<alpha>_def bis_invar_def by simp_all
  
definition mop_bis_unmake :: "'a bis \<Rightarrow> nat \<Rightarrow> 'a list nres" where
  "mop_bis_unmake \<equiv> \<lambda>(xs,l) tag. mop_al_combine xs tag"
  
lemma mop_bis_unmake_correct[refine_vcg]: "length xs = tag \<Longrightarrow> mop_bis_unmake (xs,l) tag \<le> SPEC (\<lambda>r. r=xs)"  
  by (auto simp: mop_bis_unmake_def mop_al_combine_def)
  
  













subsection \<open>Using WITH_SPLIT_ro for Karatsuba on array lists\<close>

definition karatsuba_with_split_aux :: "big_int \<Rightarrow> big_int 
  \<Rightarrow> (nat \<Rightarrow> big_int \<Rightarrow> big_int \<Rightarrow> big_int \<Rightarrow> big_int \<Rightarrow> big_int nres) 
  \<Rightarrow> big_int nres"
  where "karatsuba_with_split_aux ai bi p \<equiv> do {
    ASSERT (length ai \<ge> 2);
    ASSERT (length bi \<ge> 2);
    let m = min (length ai) (length bi) div 2;

    ci \<leftarrow> WITH_SPLIT_ro m ai (\<lambda> ai_right ai_left. do {
      ci \<leftarrow> WITH_SPLIT_ro m bi (\<lambda> bi_right bi_left. do {

        a\<^sub>r \<leftarrow> big_int_trim ai_right;
        a\<^sub>l \<leftarrow> big_int_trim ai_left;

        b\<^sub>r \<leftarrow> big_int_trim bi_right;
        b\<^sub>l \<leftarrow> big_int_trim bi_left;

        res \<leftarrow> p m a\<^sub>l a\<^sub>r b\<^sub>l b\<^sub>r;
        RETURN res
      });
      RETURN ci
    });
    RETURN ci
  }"


definition karatsuba_with_split :: "big_int \<Rightarrow> big_int \<Rightarrow> big_int nres"
  where "karatsuba_with_split ai bi \<equiv> karatsuba_RECT_base
  (\<lambda> ai bi kara. karatsuba_with_split_aux ai bi (karatsuba_recurse kara))
  (ai, bi)" 

lemma refine_Id_rel: "a \<le> (\<Down> Id) b \<Longrightarrow> (a \<le> b)"
  by simp

lemma big_int_trim_take_refine: "m < length ai \<Longrightarrow> big_int_trim (take m ai) \<le> \<Down>Id (big_int_take m ai)"  
  unfolding big_int_take_def big_int_length_def
  by auto

lemma big_int_trim_drop_refine: "m < length ai \<Longrightarrow> big_int_trim (drop m ai) \<le> \<Down>Id (big_int_drop m ai)"  
  unfolding big_int_drop_def big_int_length_def
  by auto
  
    
lemma karatsuba_with_split_refine_aux[refine]:
  assumes R: "kara1 \<le> kara2" 
  shows "karatsuba_with_split_aux ai bi kara1 \<le> (\<Down> Id) (karatsuba_aux ai bi kara2)"
proof -
  from R have "(kara1, kara2) \<in> Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
    by (auto simp: le_fun_def nres_rel_def)
  note [refine] = this[param_fo, THEN nres_relD]
  
  show ?thesis
    unfolding karatsuba_with_split_aux_def karatsuba_aux_def
    unfolding WITH_SPLIT_ro_def
    apply simp
    apply (rule refine_IdD)
    apply (refine_rcg big_int_trim_take_refine big_int_trim_drop_refine)
    by simp_all
qed
  
(*  
  apply (rule refine)
  apply (rule refine)
  apply (rule refine)
  subgoal by simp
  apply (rule refine)
  subgoal by simp
  apply (rule remove_Let_refine)
  apply (rule remove_Let_refine)

  apply (rule Let_refine'[where R=Id])
  subgoal by simp
  unfolding WITH_SPLIT_ro_def
  apply (rewrite while.imonad2)
  apply (rule refine)
  subgoal by simp
  apply (rule intro_Let_refine)
  apply (rule intro_Let_refine)
  apply (rewrite while.imonad2)
  apply (rule refine)
  subgoal by simp
  apply (rule intro_Let_refine)
  apply (rule intro_Let_refine)

  apply (rule bind_refine[where R'=Id])
  subgoal unfolding big_int_take_def 
    by (clarsimp simp: big_int_length_def)

  apply (rule bind_refine[where R'=Id])
  subgoal unfolding big_int_drop_def
    by (clarsimp simp: big_int_length_def)

  apply (rule bind_refine[where R'=Id])
  subgoal unfolding big_int_take_def 
    by (clarsimp simp: big_int_length_def)

  apply (rule bind_refine[where R'=Id])
  subgoal unfolding big_int_drop_def
    by (clarsimp simp: big_int_length_def)

  apply clarsimp

  subgoal for ai_r ai_l bi_r bi_l
    apply (drule le_funD[of "kara1" "kara2" "(min (length ai) (length bi) div 2)"])
    apply (drule le_funD[of "_" "_" "ai_l"])
    apply (drule le_funD[of "_" "_" "ai_r"])
    apply (drule le_funD[of "_" "_" "bi_l"])
    apply (drule le_funD[of "_" "_" "bi_r"])
    by simp
  done
*)

lemma karatsuba_recurse_refine:
  "(\<And>a b. kara1 (a, b) \<le> kara2 (a, b)) \<Longrightarrow>
    (karatsuba_recurse kara1) \<le> (karatsuba_recurse kara2)"
  unfolding karatsuba_recurse_def
  apply (rule le_funI)+
  apply (rule refine_Id_rel; rule bind_refine[where R'=Id]; clarsimp)+
  done

lemma karatsuba_with_split_refine': 
  "\<lbrakk>(ai, a) \<in> big_int_rel; (bi, b) \<in> big_int_rel \<rbrakk>
   \<Longrightarrow> karatsuba_with_split ai bi \<le> (\<Down> Id) (karatsuba ai bi)"
  unfolding karatsuba_with_split_def karatsuba_def karatsuba_RECT_base_def
  apply (rule RECT_refine[where R=Id])
  subgoal
    unfolding karatsuba_with_split_aux_def karatsuba_recurse_def
    apply refine_mono
    done
	subgoal by simp
  apply refine_vcg
  apply simp_all
  apply clarsimp
  apply (drule karatsuba_recurse_refine)
  apply (rule refine_Id_rel)
  apply (rule karatsuba_with_split_refine_aux)
  by simp
 

lemma karatsuba_with_split_refine:
  "\<lbrakk>(ai, a) \<in> big_int_rel; (bi, b) \<in> big_int_rel \<rbrakk>
   \<Longrightarrow> karatsuba_with_split ai bi \<le> (karatsuba ai bi)"
  using karatsuba_with_split_refine' refine_Id_rel by blast
  
(*
  Slice: 
    - Limb List
    - Slice Length

type_synonym big_int_slice = "big_int * nat"

definition big_int_slice_invar :: "big_int_slice \<Rightarrow> bool"
  where "big_int_slice_invar \<equiv> (\<lambda>(bi, l). l \<le> length bi)"

fun slice_big_int :: "big_int \<Rightarrow> big_int_slice"
  where "slice_big_int ai = (ai, big_int_length ai)"

fun extract_slice :: "big_int_slice \<Rightarrow> big_int"
  where "extract_slice (ai, len) = take len ai"

definition "big_int_slice_rel \<equiv> br extract_slice big_int_slice_invar"

definition "bis_len \<equiv> \<lambda>(bi,l). l"

definition "bis_dest \<equiv> \<lambda>(bi,l). (bi,l)"
definition "bis_make bi l \<equiv> do { ASSERT (l\<le>length bi); RETURN (bi,l) }"


definition "WITH_SPLIT_ro_bis i bis m \<equiv> doN {
  let (xs,len) = bis;
  ASSERT (i<len);
  WITH_SPLIT_ro i xs (\<lambda>xs\<^sub>1 xs\<^sub>2. do {
    let bis\<^sub>1 = (xs\<^sub>1,i);
    let len\<^sub>2 = len-i;
    ASSERT (len\<^sub>2 \<le> length xs\<^sub>2);
    let bis\<^sub>2 = (xs\<^sub>2,len-i);
    m bis\<^sub>1 bis\<^sub>2
  })
}"  

(* Monotonicity setup *)
lemma WITH_SPLIT_ro_bis_mono[refine_mono]: 
  "\<lbrakk>\<And>a b. f a b \<le> f' a b\<rbrakk> \<Longrightarrow> WITH_SPLIT_ro_bis xs n f \<le> WITH_SPLIT_ro_bis xs n f'"
  unfolding WITH_SPLIT_ro_bis_def
  by refine_mono

lemma WITH_SPLIT_ro_bis_mono_flat[refine_mono]: 
  "\<lbrakk>\<And>a b. flat_ge (f a b) (f' a b)\<rbrakk> \<Longrightarrow> flat_ge (WITH_SPLIT_ro_bis xs n f) (WITH_SPLIT_ro_bis xs n f')"
  unfolding WITH_SPLIT_ro_bis_def
  by refine_mono



(* TODO: make this not copy arrays *)
definition big_int_slice_add :: "big_int_slice \<Rightarrow> big_int_slice \<Rightarrow> big_int nres"
  where "big_int_slice_add ais bis = big_int_add (extract_slice ais) (extract_slice bis)"

lemma big_int_slice_add_refine[refine]: "\<lbrakk>(ais, ai) \<in> big_int_slice_rel; (bis, bi) \<in> big_int_slice_rel\<rbrakk>
  \<Longrightarrow> big_int_slice_add ais bis \<le> big_int_add ai bi"
  unfolding big_int_slice_add_def big_int_slice_rel_def in_br_conv big_int_slice_invar_def
  by simp

definition karatsuba_slice :: "big_int_slice \<Rightarrow> big_int_slice \<Rightarrow> big_int nres"
  where "karatsuba_slice \<equiv> (\<lambda>ai bi. 
  RECT (\<lambda> karatsuba (ai, bi). do {
		if bis_len ai = 0 then RETURN big_int0
		else if bis_len bi = 0 then RETURN big_int0
		else if bis_len ai = 1 then do {ail \<leftarrow> big_int_small_to_limb ai; big_int_mult_limb bi ail}
		else if bis_len bi = 1 then do {bil \<leftarrow> big_int_small_to_limb bi; big_int_mult_limb ai bil}
    else do {
      ASSERT (al \<ge> 2);
      ASSERT (bl \<ge> 2);
      \<comment> \<open>TODO: which is better min or max\<close>
			let m = min al bl div 2; \<comment> \<open>find midpoint: B = limb_sz ^ m \<close>
      ASSERT (m < bl);
      ASSERT (m < al);

      let al_left = m;
      let bl_left = m;
      let al_right = al - m;
      let bl_right = bl - m;

      \<comment> \<open>TODO: WITH_SPLIT requires m to be in range\<close>

      ci \<leftarrow> WITH_SPLIT_ro m ai (\<lambda> ai_left ai_right. do {
        ci \<leftarrow> WITH_SPLIT_ro m bi (\<lambda> bi_left bi_right. do {
          ai_sum \<leftarrow> big_int_slice_add (ai_left, al_left) (ai_right, al_right);
          bi_sum \<leftarrow> big_int_slice_add (bi_left, bl_left) (bi_right, bl_right);
    
          z_2 \<leftarrow> karatsuba ((ai_left, al_left), (bi_left, bl_left));
    
          z_0 \<leftarrow> karatsuba ((ai_right, al_right), (bi_right, bl_right));
          z_sum \<leftarrow> big_int_add z_2 z_0;
          
          let ai_sum_slice = slice_big_int ai_sum;
          let bi_sum_slice = slice_big_int bi_sum;
    
          z_3 \<leftarrow> karatsuba (ai_sum_slice, bi_sum_slice);
    
          \<comment> \<open>ASSERT z_3 \<ge> z_sum ; (* TODO: add comparator operhr_comp (hr_comp bis_raw_assn bis_rel) (\<langle>the_pure ?A\<rangle>list_rel)ator for big_int*)\<close> 
          z_1 \<leftarrow> big_int_sub_compl z_3 z_sum;
    
          z_1 \<leftarrow> big_int_rshift m z_1;
    
          aux \<leftarrow> big_int_add z_1 z_0;
          z_2 \<leftarrow> big_int_rshift (2*m) z_2;
    
          res \<leftarrow> big_int_add aux z_2;

          RETURN res
        });
        RETURN ci
      });hr_comp (hr_comp bis_raw_assn bis_rel) (\<langle>the_pure ?A\<rangle>list_rel)

      RETURN ci
    }
}) ((ai, al), (bi, bl)))"

find_theorems "RECT _ _ \<le> RECT _ _ "

thm "while.RECT_mono_ref"

find_theorems "_ = _" name: "rel"

lemmas [refine_dref_RELATES] = RELATESI[of big_int_slice_rel]

lemmas [refine] = big_int_drop_correct_eq big_int_take_correct_eq big_int_add_correct big_int_sub_compl_correct 
		big_int_rshift_correct_sqr big_int_rshift_correct_eq big_int_eq_correct big_int_mult_limb_correct


lemma karatsuba_slice_refine: 
  assumes 
    "(ais, ai) \<in> big_int_slice_rel" 
    "(bis, bi) \<in> big_int_slice_rel"
  shows 
    "karatsuba_slice ais bis \<le> (karatsuba ai bi)"
  unfolding karatsuba_slice_def karatsuba_def
  apply clarsimp
  apply refine_rcg
  oops
*)

section \<open>Define Karatsuba on Slices and refine to algorithm on lists\<close>

type_synonym BI_s = "limb bis"
definition "BI_s_\<alpha> xs \<equiv> big_int_\<alpha> (bis_\<alpha> xs)"

definition big_int_slice_take :: "nat \<Rightarrow> BI_s \<Rightarrow> BI_s"
  where "big_int_slice_take \<equiv> (\<lambda>n (ai, l). (ai, min n l))"

lemma big_int_slice_take_abs: "(ais, ai) \<in> bis_rel \<Longrightarrow> BI_s_\<alpha> (big_int_slice_take idx ais) = big_int_\<alpha> (take idx ai)"
  unfolding BI_s_\<alpha>_def big_int_slice_take_def bis_\<alpha>_def bis_rel_def bis_invar_def in_br_conv
  by fastforce

definition big_int_slice_trim_done :: "BI_s \<Rightarrow> bool nres" 
  where "big_int_slice_trim_done ais \<equiv> do {
    if bis_len ais = 0 then RETURN True else do {
      last_l \<leftarrow> bis_last ais;
      RETURN (\<not> last_l = 0)
    }
  }"

lemma bis_last_refine': "(ais, ai) \<in> bis_rel \<Longrightarrow> bis_last ais \<le> (\<Down>Id) (mop_list_last ai)"
  using bis_last_refine[param_fo, of ais ai] nres_rel_def
  by blast

lemma bis_last_aux: "(ais, ai) \<in> bis_rel \<Longrightarrow>
   0 < bis_len ais \<Longrightarrow> bis_get ais (bis_len ais - Suc 0) \<le> RES {last ai}"
  unfolding bis_rel_def in_br_conv bis_\<alpha>_def bis_invar_def bis_len_def bis_get_def
  apply clarsimp
  apply (refine_vcg)
  apply simp
  using last_take_nth_conv by force

lemma bis_last_refine'': "(ais, ai) \<in> bis_rel \<Longrightarrow> bis_len ais > 0 \<Longrightarrow> bis_last ais \<le> (\<Down> Id) (RETURN (last ai))"
  unfolding bis_last_def
  apply (refine_rcg)
  by (simp add: bis_last_aux)
  
lemma bis_len_refine': "(ais, ai) \<in> bis_rel \<Longrightarrow> bis_len ais = op_list_length ai"
  using bis_len_refine[param_fo]
  by blast

lemma return_or_as_if: "RETURN (big_int_length ai = 0 \<or> big_int_last_limb ai \<noteq> 0) = 
    (if big_int_length ai = 0 then RETURN True else RETURN (big_int_last_limb ai \<noteq> 0))"
  by force

lemma spec_eq_rel_id: "SPEC ((=) x) = (\<Down> Id) (RETURN x)" by force

lemma big_int_slice_trim_done_refine:
  "(ais, ai) \<in> bis_rel \<Longrightarrow> big_int_slice_trim_done ais \<le> (\<Down> Id) (RETURN (big_int_length ai = 0 \<or> big_int_last_limb ai \<noteq> 0))"
  unfolding big_int_slice_trim_done_def
  apply (rewrite return_or_as_if)
  apply (rule if_refine)
  using bis_len_refine' big_int_length_def apply fastforce
  apply simp
  apply (rule intro_bind_refine_id[where m'="big_int_last_limb ai"])
  apply (rewrite spec_eq_rel_id)
  using bis_last_refine'' unfolding big_int_last_limb_def apply blast
  by force

definition big_int_slice_trim :: "BI_s \<Rightarrow> BI_s nres"
  where "big_int_slice_trim ais \<equiv> do {
    done \<leftarrow> big_int_slice_trim_done ais;
    (bis, _) \<leftarrow> WHILEIT
      (\<lambda>(bis, done). BI_s_\<alpha> bis = BI_s_\<alpha> ais)
      (\<lambda>(bis, done). \<not> done)
      (\<lambda>(bis, done). do {
        ASSERT (bis_len bis > 0);
        last_l \<leftarrow> bis_last bis;
        ASSERT (last_l = 0);
        bis \<leftarrow> bis_pop bis;
        done \<leftarrow> big_int_slice_trim_done bis;
        RETURN (bis, done)
      }) (ais, done);
 
    RETURN bis
  }"

definition "big_int_slice_aux_rel \<equiv> {((bis, done), bi). 
  (bis, bi) \<in> bis_rel \<and> (done \<longleftrightarrow> (big_int_length bi = 0 \<or> big_int_last_limb bi \<noteq> 0))}"

lemma big_int_slice_aux_rel_intro: "((ail, n), ai) \<in> bis_rel \<Longrightarrow>
    (((ail, n), big_int_length ai = 0 \<or> big_int_last_limb ai \<noteq> 0), ai) \<in> big_int_slice_aux_rel"
  unfolding big_int_slice_aux_rel_def by blast


find_theorems "WHILEIT _ _ _ _ \<le> (\<Down> _) (WHILEIT _ _ _ _)"


lemma big_int_slice_trim_refine:
  "((ail, n), ai) \<in> bis_rel \<Longrightarrow> big_int_slice_trim (ail, n) \<le> (\<Down>bis_rel) (big_int_trim ai)"
  unfolding big_int_slice_trim_def big_int_trim_def
  apply (rule intro_bind_refine_id[where m'="(big_int_length ai = 0 \<or> big_int_last_limb ai \<noteq> 0)"])
  apply (rewrite spec_eq_rel_id)
  using big_int_slice_trim_done_refine apply blast
  apply (refine_vcg)
  apply (rule big_int_slice_aux_rel_intro)
  apply assumption
  subgoal unfolding big_int_slice_aux_rel_def BI_s_\<alpha>_def bis_rel_def in_br_conv bis_\<alpha>_def by blast
  apply clarsimp
  subgoal unfolding bis_len_def bis_invar_def big_int_length_def
    by (simp add: big_int_length_def big_int_slice_aux_rel_def)
  subgoal unfolding big_int_length_def big_int_slice_aux_rel_def bis_rel_def in_br_conv bis_\<alpha>_def bis_len_def 
    apply clarsimp
    by (metis (no_types, lifting) bis_invar_def bot_nat_0.not_eq_extremum case_prodE
        case_prod_conv snd_conv take_eq_Nil)
  prefer 2
  subgoal unfolding big_int_slice_aux_rel_def by fast
  apply clarsimp
  unfolding bis_last_def bis_get_def
  apply (rule refine)
  apply (refine_vcg)
  apply clarsimp
  apply (metis
      \<open>\<And>x bi b aa. ((ail, n), ai) \<in> bis_rel \<Longrightarrow> (x, bi) \<in> big_int_slice_aux_rel \<Longrightarrow> x = (aa, b) \<Longrightarrow> (aa, bi) \<in> bis_rel\<close>
      bis_invar_def bis_len_def bis_rel_def in_br_conv nz_le_conv_less old.prod.case
      prod.sel(2)) 
  unfolding big_int_slice_aux_rel_def big_int_last_limb_def big_int_length_def bis_len_def bis_rel_def in_br_conv bis_\<alpha>_def
  apply clarsimp
   apply (simp add: bis_invar_def last_take_nth_conv)
  unfolding bis_pop_def
  apply clarsimp
  apply (refine_vcg)
  unfolding big_int_slice_trim_done_def
  apply clarsimp
  apply (refine_vcg)
  apply (simp add: bis_len_def butlast_take)
    apply (simp add: bis_len_def butlast_take)
   apply (simp add: bis_invar_def)
  unfolding bis_last_def bis_get_def
  apply (refine_vcg)
  apply clarsimp
  apply (simp add: bis_invar_def bis_len_def)
  apply simp
  apply (metis (no_types, lifting) One_nat_def bis_invar_def bis_len_def
      bot_nat_0.not_eq_extremum butlast_take diff_le_self last_take_nth_conv
      old.prod.case order_trans prod.sel(2) take_eq_Nil)

  apply (simp add: bis_invar_def butlast_take)
  unfolding bis_invar_def
  by auto

lemma big_int_slice_trim_refine':
  "(ls, l) \<in> bis_rel \<Longrightarrow> big_int_slice_trim ls \<le> (\<Down>bis_rel) (big_int_trim l)"
  using big_int_slice_trim_refine
  by (metis surj_pair)


definition bis_destr :: "'a list \<times> nat \<Rightarrow> 'a list \<times> nat" where [simp]: "bis_destr bis \<equiv> bis"
definition bis_constr :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list \<times> nat" where [simp]: "bis_constr xs l \<equiv> (xs,l)"
  
definition "WITH_SPLIT_bis_ro i bis m \<equiv> doN {
  let (xs, len) = bis_destr bis;
  ASSERT(i < len);
  r\<leftarrow>WITH_SPLIT_ro i xs (\<lambda> xs\<^sub>1 xs\<^sub>2. do {
    let bis\<^sub>1 = bis_constr xs\<^sub>1 i;
    let len\<^sub>2 = len - i;
    ASSERT (len\<^sub>2 \<le> length xs\<^sub>2);
    let bis\<^sub>2 = bis_constr xs\<^sub>2 (len-i);
    r \<leftarrow> m bis\<^sub>1 bis\<^sub>2;
    let (xs\<^sub>1',_) = bis_destr bis\<^sub>1;
    let (xs\<^sub>2',_) = bis_destr bis\<^sub>2;
    unborrow xs\<^sub>1' xs\<^sub>1;
    unborrow xs\<^sub>2' xs\<^sub>2;
    RETURN r
  });
  
  let bis' = bis_constr xs len;
  unborrow bis' bis;
  
  RETURN r
}"

thm WITH_SPLIT_ro_mono

(* Monotonicity setup *)
lemma WITH_SPLIT_ro_bis_mono[refine_mono]: 
  "\<lbrakk>\<And>a b. f a b \<le> f' a b\<rbrakk> \<Longrightarrow> WITH_SPLIT_bis_ro xs n f \<le> WITH_SPLIT_bis_ro xs n f'"
  unfolding WITH_SPLIT_bis_ro_def
  by refine_mono

lemma WITH_SPLIT_ro_bis_mono_flat[refine_mono]: 
  "\<lbrakk>\<And>a b. flat_ge (f a b) (f' a b)\<rbrakk> \<Longrightarrow> flat_ge (WITH_SPLIT_bis_ro xs n f) (WITH_SPLIT_bis_ro xs n f')"
  unfolding WITH_SPLIT_bis_ro_def
  by refine_mono

definition big_int_slice_add_invar :: "BI_s \<Rightarrow> BI_s \<Rightarrow> (big_int \<times> nat \<times> limb) \<Rightarrow> bool"
  where "big_int_slice_add_invar ai bi \<equiv> (\<lambda>(ci, idx, cr). 
    cr \<in> {0, 1} \<and>
    idx = length ci \<and>
    idx < max (bis_len ai) (bis_len bi) + 2 \<and>
    BI_s_\<alpha> (big_int_slice_take idx ai) +
    BI_s_\<alpha> (big_int_slice_take idx bi) = 
    big_int_to_nat ci + limb_nat cr * limb_sz ^ idx)"



definition bis_get_or_zero :: "BI_s \<Rightarrow> nat \<Rightarrow> limb nres"
  where "bis_get_or_zero ais n \<equiv> (if n < bis_len ais then bis_get ais n else RETURN 0)"

lemma "(ais, ai) \<in> bis_rel \<Longrightarrow> bis_get_or_zero ais i \<le> (\<Down> Id) (RETURN (nth_default 0 ai i))"
  unfolding bis_get_or_zero_def bis_get_def bis_len_refine' nth_default_def
  apply refine_vcg
  unfolding bis_rel_def in_br_conv bis_\<alpha>_def bis_invar_def
  by simp+

lemma bis_len_eq: "(a, b) \<in> bis_rel \<Longrightarrow> bis_len a = length b"
  using bis_len_refine[param_fo] by fastforce

lemma bis_len_eq': "((a,b), c) \<in> bis_rel \<Longrightarrow> bis_len (a, b) = length c"
  using bis_len_refine[param_fo] by fastforce

lemma bis_get_or_zero_refine: "(ais, ai) \<in> bis_rel \<Longrightarrow> bis_get_or_zero ais n \<le> (\<Down> Id) (RETURN (get_or_zero ai n))"
  unfolding bis_get_or_zero_def get_or_zero_def bis_len_eq bis_get_def mop_list_get_alt pre_list_get_def
  unfolding bis_rel_def in_br_conv bis_\<alpha>_def
  apply (refine_vcg)
  by auto

lemma bis_get_or_zero_refine': "(ais, ai) \<in> bis_rel \<Longrightarrow> bis_get_or_zero ais n \<le> Refine_Basic.SPEC
          (\<lambda>c. (c, get_or_zero ai n) \<in> Id)"
  using bis_get_or_zero_refine 
  by (meson RETURN_rule order_trans pair_in_Id_conv refine_IdD)
  
definition big_int_slice_add_loop :: "BI_s \<Rightarrow> BI_s \<Rightarrow> big_int nres"
  where "big_int_slice_add_loop ais bis \<equiv> do {
    (ci, _, _) \<leftarrow> WHILEIT 
      (big_int_slice_add_invar ais bis)
      (\<lambda>(ci, idx, cr). idx < max (bis_len ais) (bis_len bis) \<or> (cr > 0))
      (\<lambda>(ci, idx, cr). do {
        ai \<leftarrow> bis_get_or_zero ais idx;
        bi \<leftarrow> bis_get_or_zero bis idx;
        let (r, cr) = add_carry ai bi cr;


        ci_next \<leftarrow> bi_append ci r;
        \<comment> \<open>TODO: change this to use ASSERT idx + 1 < length bi_next\<close>

        ASSERT (idx + 1 \<le> length ci_next);

        let idx = idx + 1;

        RETURN (ci_next, idx, cr)
      }) (big_int0, 0, 0);
    RETURN ci
  }"


definition big_int_slice_add :: "BI_s \<Rightarrow> BI_s \<Rightarrow> big_int nres"
  where "big_int_slice_add ais bis \<equiv> do {
    ci \<leftarrow> big_int_slice_add_loop ais bis;
		ci \<leftarrow> big_int_trim ci;
    RETURN ci
  }"

thm bis_len_refine[param_fo]



find_theorems "Let" name: "refine"

lemma eq_refine: "(ci, cia) \<in> Id \<Longrightarrow>
       big_int_trim ci \<bind> Refine_Basic.RETURN
       \<le> \<Down> Id (big_int_trim cia \<bind> Refine_Basic.RETURN)"
  by auto

lemma eq_rel: "(a, a) \<in> Id" by auto (* IdI *)
lemma rel_Id_intro: "a \<le> b \<Longrightarrow> a \<le> \<Down> Id b" (* refine_IdI *) oops
lemma "a \<le> \<Down> Id a" (* Id_refine *) oops

lemma big_int_slice_add_refine: "(ais, ai) \<in> bis_rel \<Longrightarrow> (bis, bi) \<in> bis_rel \<Longrightarrow>
    big_int_slice_add ais bis \<le> (\<Down> Id) (big_int_add ai bi)"
  unfolding big_int_slice_add_def big_int_add_def 
  apply (rule remove_Let_refine)
  apply (rule refine)
  prefer 2
  apply (rule eq_refine)
  apply assumption
  unfolding big_int_slice_add_loop_def big_int_add_loop_def big_int_slice_add_invar_def
    big_int_add_loop_invar_def big_int_add_cond_def big_int_slice_take_abs bis_len_eq
  apply (refine_vcg)
  apply (rule eq_rel)
  apply simp_all
  apply fastforce
  apply fastforce
  apply fastforce
  apply fastforce
  apply (rule bis_get_or_zero_refine')
  apply assumption
  apply (rule bis_get_or_zero_refine')
  apply assumption
  apply clarsimp
  apply (rule Id_refine)
  apply clarsimp
  by simp

definition big_int_mult_limb_slice_aux :: "BI_s \<Rightarrow> limb \<Rightarrow> big_int nres" 
  where "big_int_mult_limb_slice_aux ais c \<equiv> do {
    (bi, idx, cr) \<leftarrow> WHILEIT
        (\<lambda>(bi, idx, cr). 
          length bi = idx \<and>
          idx \<le> bis_len ais + 1 \<and>
          BI_s_\<alpha> (big_int_slice_take idx ais) * limb_nat c = 
          big_int_\<alpha> bi + limb_nat cr * limb_sz ^ idx
        )
        (\<lambda>(bi, idx, cr). idx < bis_len ais \<or> cr \<noteq> 0)
        (\<lambda>(bi, idx, cr). do {
          aidx \<leftarrow> bis_get_or_zero ais idx;
          let (rs, cr) = mul_add aidx c cr;
  
          ASSUME (sepref_sorry_that(length bi+1 < max_snat 64));
          ASSERT(idx + 1 < max_snat 64);
    
          bi_next \<leftarrow> bi_append bi rs;
          \<comment> \<open>TODO: change this to use ASSERT idx + 1 < length bi_next\<close>

          let idx = idx + 1;
  
          RETURN (bi_next, idx, cr)
        })
        (big_int0, 0, 0);
    RETURN bi
  }"

definition big_int_mult_limb_slice :: "BI_s \<Rightarrow> limb \<Rightarrow> big_int nres"
  where "big_int_mult_limb_slice ais c \<equiv> do {
    bi \<leftarrow> big_int_mult_limb_slice_aux ais c;
    bi \<leftarrow> big_int_trim bi;
    RETURN bi
  }"

definition big_int_mult_limb_slice_small :: "BI_s \<Rightarrow> BI_s \<Rightarrow> big_int nres"
  where "big_int_mult_limb_slice_small ais bis \<equiv> do {
    ASSERT (bis_len ais = 1);
    ail \<leftarrow> bis_last ais;
    res \<leftarrow> big_int_mult_limb_slice bis ail;
    RETURN res
  }"

lemma big_int_slice_get_0: 
  "(ais, ai) \<in> bis_rel \<Longrightarrow> length ai = 1  \<Longrightarrow> bis_get ais 0 \<le> \<Down> Id (big_int_small_to_limb ai)"
  unfolding bis_get_def big_int_small_to_limb_def
  apply refine_vcg
  apply clarsimp 
  unfolding bis_rel_def in_br_conv bis_\<alpha>_def bis_invar_def apply simp
  apply clarsimp
  unfolding hd_conv_nth
  by blast

lemma big_int_slice_last:
  "(ais, ai) \<in> bis_rel \<Longrightarrow> length ai = 1  \<Longrightarrow> bis_last ais \<le> \<Down> Id (big_int_small_to_limb ai)"
  unfolding bis_last_def bis_len_eq
  apply clarsimp
  apply (rule refine_IdD)
  apply (refine_vcg big_int_slice_get_0)
  by simp

  
find_theorems "bis_get_or_zero"

lemma big_int_mult_limb_slice_small_refine: "(ais, ai) \<in> bis_rel \<Longrightarrow> (bis, bi) \<in> bis_rel \<Longrightarrow>
  big_int_mult_limb_slice_small ais bis \<le> (\<Down> Id) (big_int_mult_small ai bi)"
  unfolding big_int_mult_limb_slice_small_def big_int_mult_small_def bis_len_eq
  apply (refine_vcg big_int_slice_last) 
  unfolding big_int_mult_limb_slice_def big_int_mult_limb_def
  apply (refine_vcg)
  unfolding big_int_mult_limb_slice_aux_def big_int_mult_limb_aux_def big_int_mult_limb_invar_def bis_len_eq big_int_slice_take_abs
  apply (refine_vcg)
  apply (rule eq_rel)
  apply clarsimp
  apply simp_all
  apply fastforce
  apply fastforce
  apply (rule bis_get_or_zero_refine';assumption)
  apply simp
  apply (rule Id_refine)
  apply fastforce
  apply (rule eq_rel)
  apply simp
  apply (rule Id_refine)
  by simp

lemma big_int_mult_limb_slice_refine: 
  "(ais, ai) \<in> bis_rel \<Longrightarrow> big_int_mult_limb_slice ais c \<le> (\<Down> Id) (big_int_mult_limb ai c)"
  unfolding big_int_mult_limb_slice_def big_int_mult_limb_def 
  apply (rule refine)
  prefer 2
  apply (rule eq_refine)
  apply assumption
  unfolding big_int_mult_limb_slice_aux_def big_int_mult_limb_aux_def big_int_mult_limb_invar_def
    big_int_slice_take_abs bis_len_eq
  apply (refine_vcg)
  apply (rule eq_rel)
  apply simp_all
  apply fastforce
  apply fastforce
  apply fastforce
  apply (rule bis_get_or_zero_refine')
  apply assumption
  apply clarsimp
  apply (rule Id_refine)
  by simp

definition karatsuba_slice_basecase
  where "karatsuba_slice_basecase recurse \<equiv> do {
  (\<lambda> kara (ais, bis). do {
          if bis_len ais = 0 then RETURN big_int0 
    else  if bis_len bis = 0 then RETURN big_int0 
    else  if bis_len ais = 1 then big_int_mult_limb_slice_small ais bis 
    else  if bis_len bis = 1 then big_int_mult_limb_slice_small bis ais 
    else  recurse ais bis kara
  })
}"

definition karatsuba_slice_recurse
  where "karatsuba_slice_recurse kara m ais_l ais_r bis_l bis_r \<equiv> do {
    ai_sum \<leftarrow> big_int_slice_add ais_l ais_r;
    bi_sum \<leftarrow> big_int_slice_add bis_l bis_r;

    z_2 \<leftarrow> kara (ais_l, bis_l);
    z_0 \<leftarrow> kara (ais_r, bis_r);
    z_sum \<leftarrow> big_int_add z_2 z_0;
    
    
    (ai_sum,taga) \<leftarrow> mop_bis_make ai_sum;
    (bi_sum,tagb) \<leftarrow> mop_bis_make bi_sum;
    z_3 \<leftarrow> kara (ai_sum, bi_sum);
    ai_sum \<leftarrow> mop_bis_unmake ai_sum taga;
    bi_sum \<leftarrow> mop_bis_unmake bi_sum tagb;

    z_1 \<leftarrow> big_int_sub_compl z_3 z_sum;

    z_1 \<leftarrow> big_int_rshift m z_1;

    aux \<leftarrow> big_int_add z_1 z_0;
    z_2 \<leftarrow> big_int_rshift (2*m) z_2;

    res \<leftarrow> big_int_add aux z_2;

    RETURN res
  }"

lemma mop_bis_make_unfold: "mop_bis_make xs = RETURN ((xs, length xs), length xs)"  
  unfolding mop_bis_make_def mop_al_split_def by simp
  
lemma mop_bis_unmake_unfold: "mop_bis_unmake xs tag = do {ASSERT (length (fst xs) = tag); RETURN (fst xs) }"  
  unfolding mop_bis_unmake_def mop_al_combine_def by (cases xs) simp
  
  
lemma karatsuba_slice_recurse_refine:
  assumes 
    "\<And>ls l rs r. (ls, l) \<in> bis_rel \<Longrightarrow> (rs, r) \<in> bis_rel \<Longrightarrow> kara (ls, rs) \<le> (\<Down> Id) (kara' (l, r))"
    "(ais_l, ai_l) \<in> bis_rel"  
    "(ais_r, ai_r) \<in> bis_rel"  
    "(bis_l, bi_l) \<in> bis_rel"  
    "(bis_r, bi_r) \<in> bis_rel"
  shows 
  "karatsuba_slice_recurse kara m ais_l ais_r bis_l bis_r \<le> (\<Down> Id) 
   (karatsuba_recurse kara' m ai_l ai_r bi_l bi_r)"
  unfolding karatsuba_slice_recurse_def karatsuba_recurse_def mop_bis_make_unfold mop_bis_unmake_unfold
  apply (simp del: conc_Id)
  using assms
  apply (refine_rcg big_int_slice_add_refine)
  apply rprems
  apply assumption+
  apply (drule IdD; clarify; rule Id_refine)+
  apply rprems
  apply (simp add: bis_make_refine)
  apply (simp add: bis_make_refine)
  by (drule IdD; clarify; rule Id_refine)+

definition karatsuba_slice_split 
  where "karatsuba_slice_split \<equiv> (\<lambda> ais bis kara. do {
    ASSERT (bis_len ais \<ge> 2);
    ASSERT (bis_len bis \<ge> 2);

    let m = min (bis_len ais) (bis_len bis) div 2;
    
    WITH_SPLIT_bis_ro m ais (\<lambda> ais_r ais_l. do {
      WITH_SPLIT_bis_ro m bis (\<lambda> bis_r bis_l. do {
        ais_r \<leftarrow> big_int_slice_trim ais_r;
        ais_l \<leftarrow> big_int_slice_trim ais_l;
    
        bis_r \<leftarrow> big_int_slice_trim bis_r;
        bis_l \<leftarrow> big_int_slice_trim bis_l;

        res \<leftarrow> karatsuba_slice_recurse kara m ais_l ais_r bis_l bis_r;
        RETURN res
      })
    })
})"


definition karatsuba_slice_with_split :: "BI_s \<Rightarrow> BI_s \<Rightarrow> big_int nres"
  where "karatsuba_slice_with_split ais bis \<equiv> 
  RECT (karatsuba_slice_basecase karatsuba_slice_split)
   (ais, bis)"


definition karatsuba_slice :: "BI_s \<Rightarrow> BI_s \<Rightarrow> big_int nres"
  where "karatsuba_slice ais bis \<equiv> do {
    RECT (\<lambda> kara (ais, bis). do {
      if bis_len ais = 0 then RETURN big_int0 else
      if bis_len bis = 0 then RETURN big_int0 else
      if bis_len ais = 1 then big_int_mult_limb_slice_small ais bis else
      if bis_len bis = 1 then big_int_mult_limb_slice_small bis ais else
      do {
        ASSERT (bis_len ais \<ge> 2);
        ASSERT (bis_len bis \<ge> 2);

        let m = min (bis_len ais) (bis_len bis) div 2;
        
        WITH_SPLIT_bis_ro m ais (\<lambda> ais_r ais_l. do {
          WITH_SPLIT_bis_ro m bis (\<lambda> bis_r bis_l. do {

            ais_r \<leftarrow> big_int_slice_trim ais_r;
            ais_l \<leftarrow> big_int_slice_trim ais_l;

            bis_r \<leftarrow> big_int_slice_trim bis_r;
            bis_l \<leftarrow> big_int_slice_trim bis_l;

            ai_sum \<leftarrow> big_int_slice_add ais_l ais_r;
            bi_sum \<leftarrow> big_int_slice_add bis_l bis_r;

            z_2 \<leftarrow> kara (ais_l, bis_l);
            z_0 \<leftarrow> kara (ais_r, bis_r);
            z_sum \<leftarrow> big_int_add z_2 z_0;
            
            (ai_sum,taga) \<leftarrow> mop_bis_make ai_sum;
            (bi_sum,tagb) \<leftarrow> mop_bis_make bi_sum;
            z_3 \<leftarrow> kara (ai_sum, bi_sum);
            ai_sum \<leftarrow> mop_bis_unmake ai_sum taga;
            bi_sum \<leftarrow> mop_bis_unmake bi_sum tagb;

            z_1 \<leftarrow> big_int_sub_compl z_3 z_sum;
      
            z_1 \<leftarrow> big_int_rshift m z_1;
      
            aux \<leftarrow> big_int_add z_1 z_0;
            z_2 \<leftarrow> big_int_rshift (2*m) z_2;
      
            res \<leftarrow> big_int_add aux z_2;
    
            RETURN res
          })
        })
      }
    }) (ais, bis)
  }"

find_theorems "\<langle>Id\<rangle>list_rel"
lemma list_rel_eq: "(a, a) \<in> \<langle>Id\<rangle>list_rel" unfolding list_rel_id_simp by simp
lemma list_rel_eq': "a = b \<Longrightarrow> (a, b) \<in> \<langle>Id\<rangle>list_rel" using list_rel_eq by blast
lemma eq_Id_refine: "a = b \<Longrightarrow> a \<le> \<Down> Id b" by auto 

find_theorems "bind" "RETURN"

lemma karatsuba_slice_with_split_equiv: 
  "karatsuba_slice_with_split ais bis \<le> (\<Down> Id) (karatsuba_slice ais bis)"
  unfolding karatsuba_slice_with_split_def karatsuba_slice_def karatsuba_slice_basecase_def
    karatsuba_slice_split_def karatsuba_slice_recurse_def WITH_SPLIT_bis_ro_def bis_destr_def bis_constr_def unborrow_def
  (* Causes mismatch in program later on because of a while.imonad2 not being applied
  apply (refine_rcg)
  apply (rule IdI)
  apply (drule IdD; clarify; rule Id_refine)+
  apply (rule list_rel_eq')
  apply (drule IdD; clarify; rule Id_refine)+
  apply (rule list_rel_eq')
  apply (drule IdD; clarify; rule Id_refine)+
  apply (drule IdD)
  apply clarify
  *) 

  apply (rule refine)
  apply refine_mono
  apply (rule IdI)
  apply clarify

  (* Base cases *)
  apply (rule refine)
  subgoal by simp
  subgoal by simp
  apply (rule refine)
  subgoal by simp
  subgoal by simp
  apply (rule refine)
  subgoal by simp
  subgoal by simp
  apply (rule refine)
  subgoal by simp
  subgoal by simp

  apply clarify

  (* Asserts *)
  apply (rule refine)
  apply (rule refine)
  apply (rule refine)
  apply assumption
  apply (rule refine)
   apply assumption

  apply (rule refine)  
  apply (rule refine)

  apply clarify
  apply (rule refine)
  apply (rule refine)
   apply assumption

  (* First Split *)
  apply (rule refine)
  apply (rule refine)
  apply simp
  apply (rule list_rel_eq'; simp)

  apply (rule refine)
  apply (rule refine)
  apply (rule refine)
  apply (rule refine)
   apply assumption

  apply (rule refine)
  apply (rule refine)
  apply (rule refine)
  apply clarify
  apply (rule refine)
  apply (rule refine)
  apply assumption

  (* Second split *)
  apply (rule refine)
  apply (rule refine)
  apply blast
  apply (rule list_rel_eq'; blast)

  apply (rule refine)
  apply (rule refine)
  apply (rule refine)
  apply (rule refine)
  apply assumption

  apply (rule refine)

  apply (rule refine)
  apply (rule refine)
  apply (rule eq_Id_refine; blast)
  apply (rule refine)
  apply (rule eq_Id_refine; blast)
  apply (rule refine)
   apply (rule eq_Id_refine; blast)
  apply (rule refine)
  apply (rule eq_Id_refine; blast)
  apply clarify

  (* HERE cause of refine_rcg mismatch *)
  apply (rewrite while.imonad2)
  apply (rule refine)
  apply (rule eq_Id_refine; blast)
  apply (rule refine)
  apply (rule eq_Id_refine; blast)
  apply (rule refine)
  apply rprems
  apply blast
  apply (rule refine)
  apply rprems
  apply blast
  apply clarify
  apply (rule refine)
  apply (rule eq_Id_refine; blast)
  apply (rule refine)
  apply (rule eq_Id_refine; blast)
  
  apply (split prod.split; intro allI impI)
  apply (split prod.split; intro allI impI)
  apply (rule refine)
  apply (rule eq_Id_refine; blast)

  apply (split prod.split; intro allI impI)
  apply (split prod.split; intro allI impI)
    
  apply clarify
  apply (rule refine)
  apply rprems
  apply blast
  apply clarify
  apply (rule refine)
  apply (rule eq_Id_refine; blast)
  apply clarify
  apply (rule refine)
  apply (rule eq_Id_refine; blast)
  apply clarify
  apply (rule refine)
  apply (rule eq_Id_refine; blast)
  apply clarify
  apply (rule refine)
  apply (rule eq_Id_refine; blast)
  apply clarify
  apply (rule refine)
  apply (rule eq_Id_refine; blast)
  apply clarify
  apply (rule eq_Id_refine; blast)
  apply (rule eq_Id_refine; blast)
  apply (rule eq_Id_refine; blast)
  apply (rule eq_Id_refine; blast)
  apply (rule eq_Id_refine; blast)
  done


definition "karatsuba_slice_rel \<equiv> {((ais, bis), (ai, bi)). (ais, ai) \<in> bis_rel \<and> (bis, bi) \<in> bis_rel }"
lemma intro_karatsuba_slice_rel: "(ais, ai) \<in> bis_rel \<Longrightarrow> (bis, bi) \<in> bis_rel \<Longrightarrow> ((ais, bis), (ai, bi)) \<in> karatsuba_slice_rel" 
  unfolding karatsuba_slice_rel_def by simp

find_theorems "take" "drop"

lemma WITH_SPLIT_bis_ro_refine:
  "(ais, ai) \<in> bis_rel \<Longrightarrow> 
  (\<And>ls l rs r. (ls, l) \<in> bis_rel \<Longrightarrow> (rs, r) \<in> bis_rel \<Longrightarrow> p ls rs \<le> \<Down> R (p' l r)) \<Longrightarrow>
  (m, m') \<in> Id \<Longrightarrow>
  WITH_SPLIT_bis_ro m ais p \<le> \<Down> R (WITH_SPLIT_ro m' ai p')"
  unfolding WITH_SPLIT_bis_ro_def WITH_SPLIT_ro_def
    bis_rel_def in_br_conv bis_\<alpha>_def bis_invar_def unborrow_def
  apply refine_vcg
  apply clarsimp
  apply simp
  apply refine_vcg
  
   apply force
  apply (clarsimp simp: drop_take)
  apply (rule order_trans)
  apply rprems
  apply simp
  apply simp
  by simp
(*
  "WITH_SPLIT_bis_ro" :: "nat \<Rightarrow> 'a list \<times> nat \<Rightarrow> ('a list \<times> nat \<Rightarrow> 'a list \<times> nat \<Rightarrow> 'b nres      ) \<Rightarrow> 'b nres"

  "WITH_SPLIT_ro"     :: "nat \<Rightarrow> 'a list       \<Rightarrow> ('a list        \<Rightarrow> 'a list       \<Rightarrow> 'b nres      ) \<Rightarrow> 'b nres"
  
                          Id  \<rightarrow>  bis_rel      \<rightarrow> ( bis_rel       \<rightarrow> bis_rel       \<rightarrow> \<langle>Id\<rangle>nres_rel  ) \<rightarrow> \<langle>Id\<rangle>nres_rel
  
*)  

corollary "(WITH_SPLIT_bis_ro,WITH_SPLIT_ro) \<in> Id  \<rightarrow>  bis_rel      \<rightarrow> ( bis_rel       \<rightarrow> bis_rel       \<rightarrow> \<langle>Id\<rangle>nres_rel  ) \<rightarrow> \<langle>Id\<rangle>nres_rel"
  apply (safe)
  apply (rule nres_relI)
  apply (rule WITH_SPLIT_bis_ro_refine)
  apply auto []
  subgoal
    unfolding fun_rel_def nres_rel_def
    by force
  apply auto []
  done

find_theorems "WITH_SPLIT_ro"


(*      TODO: we need a version of this for the WITH_SPLIT_bis_ro

lemma hn_WITH_SPLIT_ro_template:
      assumes sl_assn_def: "sl_assn = hr_comp raw_array_slice_assn (\<langle>A\<rangle>list_rel)"
      assumes FR: "\<Gamma> \<turnstile> hn_ctxt sl_assn xs xsi ** hn_ctxt snat_assn n ni ** \<Gamma>\<^sub>1"
      assumes HN: "\<And>xs\<^sub>1 xsi\<^sub>1 xs\<^sub>2 xsi\<^sub>2. \<lbrakk> CP_assm (xsi\<^sub>1 = xsi) \<rbrakk> \<Longrightarrow> hn_refine 
        (hn_ctxt sl_assn xs\<^sub>1 xsi\<^sub>1 ** hn_ctxt sl_assn xs\<^sub>2 xsi\<^sub>2 ** hn_ctxt snat_assn n ni ** \<Gamma>\<^sub>1) 
        (mi xsi\<^sub>1 xsi\<^sub>2) 
        (\<Gamma>\<^sub>2 xs\<^sub>1 xsi\<^sub>1 xs\<^sub>2 xsi\<^sub>2) (R) (CP xsi\<^sub>1 xsi\<^sub>2) (m xs\<^sub>1 xs\<^sub>2)"
      assumes FR2: "\<And>xs\<^sub>1 xsi\<^sub>1 xs\<^sub>2 xsi\<^sub>2. \<Gamma>\<^sub>2 xs\<^sub>1 xsi\<^sub>1 xs\<^sub>2 xsi\<^sub>2 \<turnstile>
        hn_ctxt sl_assn xs\<^sub>1 xsi\<^sub>1 ** hn_ctxt sl_assn xs\<^sub>2 xsi\<^sub>2 ** \<Gamma>\<^sub>1'"
        
      assumes CP2: "\<And>xsi\<^sub>2. CP_simplify (CP xsi xsi\<^sub>2) (CP')"  
      shows "hn_refine 
        (\<Gamma>) 
        (ars_with_split_ro ni xsi mi) 
        (hn_ctxt sl_assn xs xsi ** \<Gamma>\<^sub>1') 
        R
        (CP') 
        (WITH_SPLIT_ro$n$xs$(\<lambda>\<^sub>2a b. m a b))"  
      unfolding autoref_tag_defs PROTECT2_def
      apply (rule hn_refine_cons_pre)
      applyS (rule FR)
      apply1 extract_hnr_invalids
      supply R = hn_WITH_SPLIT_ro_template_aux[OF sl_assn_def, where CP=CP']
      thm R
      apply (rule hn_refine_cons_cp[OF _ R])
      applyS (fri)
      apply1 extract_hnr_invalids
      apply (rule hn_refine_cons[OF _ HN])
      applyS (fri)
      applyS (simp add: CP_defs)
      applyS (sep_drule FR2; simp; rule entails_refl)
      applyS(rule entails_refl)
      focus using CP2 unfolding CP_defs apply blast solved
      applyS (simp add: hn_ctxt_def invalid_pure_recover)
      applyS (rule entails_refl)
      applyS blast
      done  
*)


lemma karatsuba_slice_refine:
  assumes 
    "(ais, ai) \<in> bis_rel"
    "(bis, bi) \<in> bis_rel"
  shows 
    "karatsuba_slice ais bis \<le> (\<Down> Id) (karatsuba_with_split ai bi)"
  unfolding karatsuba_slice_def karatsuba_with_split_def karatsuba_RECT_base_def 
  apply refine_vcg
  using assms
  apply (rule intro_karatsuba_slice_rel)
  unfolding karatsuba_slice_rel_def 
  apply clarsimp
  apply (fastforce simp: bis_len_eq)
  apply (fastforce simp: bis_len_eq)
  apply (fastforce simp: bis_len_eq)
  apply (rule big_int_mult_limb_slice_small_refine)
  apply blast
  apply blast
  apply (fastforce simp: bis_len_eq)
  apply (rule big_int_mult_limb_slice_small_refine)
  apply blast
  apply blast
  apply fastforce
  apply fastforce
  unfolding karatsuba_with_split_aux_def karatsuba_recurse_def mop_bis_make_unfold mop_bis_unmake_unfold
  apply (simp del: conc_Id)
  apply (refine_vcg)
  apply simp
  apply auto
  apply (rule refine_IdD)
  apply (rule WITH_SPLIT_bis_ro_refine)
  apply assumption
  apply (rule WITH_SPLIT_bis_ro_refine)
  apply assumption
  apply (refine_vcg big_int_slice_trim_refine' big_int_slice_add_refine)
  apply simp
  apply (rule refine_IdI)
  apply force
  apply (rule refine_IdI)
  apply force
  apply simp_all
  apply (rule refine_IdI; simp)
  apply (rule refine_IdI)
  apply rprems
  apply (simp add: bis_make_refine)
  apply (simp; rule refine_IdI; simp)
  unfolding bis_len_eq'
  apply (rule refine_IdI; simp)+
  apply (rule refine_IdD; simp)
  apply simp
  apply simp
  done


lemma karatsuba_slice_with_split_refine':"(ais, ai) \<in> bis_rel \<Longrightarrow> (bis, bi) \<in> bis_rel \<Longrightarrow> 
  karatsuba_slice_with_split ais bis \<le> (\<Down> Id) (karatsuba_with_split ai bi)"
  using karatsuba_slice_refine karatsuba_slice_with_split_equiv
  by (meson conc_trans_additional(2))


corollary karatsuba_slice_with_split_correct: "(ais, ai) \<in> bis_rel \<Longrightarrow> (ai, a) \<in> big_int_rel \<Longrightarrow> (bis, bi) \<in> bis_rel \<Longrightarrow> (bi, b) \<in> big_int_rel \<Longrightarrow>
  karatsuba_slice_with_split ais bis \<le> (\<Down> big_int_rel) (RETURN (a * b))"
  apply (rule conc_trans_additional(2))
  apply (rule karatsuba_slice_with_split_refine'; assumption+)
  apply (rule conc_trans_additional(2))
  apply (rule karatsuba_with_split_refine'; assumption+)
  using karatsuba_correct 
  by presburger


end