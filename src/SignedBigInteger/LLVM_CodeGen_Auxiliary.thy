theory LLVM_CodeGen_Auxiliary
  imports Basic "../LLVM_CodeGen" 
begin
text "This file includes some required low-level implementations of essential functions on signed big ints.
  The main reason for why these functions are needed is that unpacking a tuple @{typ signed_big_int} requires destroying the argument"
(* `sbi` \<sim> "signed big integer" *)
abbreviation "sbi_aux_assn \<equiv> bi_aux_assn \<times>\<^sub>a bool1_assn"
definition "sbi_assn \<equiv> hr_comp sbi_aux_assn signed_big_int_rel"

sepref_def \<sigma>_impl is "RETURN o \<sigma>" :: "sbi_aux_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  unfolding \<sigma>_def snd_def
  by sepref

(*you need this for the base operations*)
definition length_fst where
  \<open>length_fst a = length (fst a)\<close>

definition length_fst_impl :: \<open>(64 word \<times> 64 word \<times> 64 word ptr) \<times> 1 word \<Rightarrow> 64 word llM\<close> where
  \<open>length_fst_impl = (\<lambda>al. 
        let ((l,c,a),_) = al in Mreturn l
      )\<close>

(*I thought this would just work out of the box with sepref*)
lemma [sepref_fr_rules]:
  \<open>(length_fst_impl, RETURN o length_fst) \<in> sbi_aux_assn\<^sup>k  \<rightarrow>\<^sub>a snat_assn\<close>
  unfolding length_fst_def length_fst_impl_def
  apply sepref_to_hoare
  apply vcg_all
  apply (auto simp: ENTAILS_def pure_true_conv entails_def bool1_rel_def
      hr_comp_def bool.rel_def pred_lift_def) 
  unfolding pred_lift_def
  apply (auto simp: ENTAILS_def pure_true_conv entails_def bool1_rel_def
      hr_comp_def bool.rel_def pred_lift_def)

  apply (auto simp: al_assn_def hr_comp_def arl_assn_def arl_assn'_def
      snat.assn_is_rel sep_conj_def pure_def snat.rel_def br_def
      pred_lift_def snat_rel_def dest: list_rel_imp_same_length)
  done

lemma [llvm_code,llvm_inline]: \<open>length_fst_impl = (\<lambda>al. 
        let (x,_) = al ; (l,c,a) = x in Mreturn l
      )\<close>
  unfolding length_fst_impl_def by auto

(*
export_llvm length_fst_impl file "/tmp/test.ll"
*)

definition nth_fst where
  \<open>nth_fst a i = (fst a) ! i\<close>

thm arl_nth_def
definition nth_fst_impl :: \<open>(64 word \<times> 64 word \<times> 64 word ptr) \<times> 1 word \<Rightarrow> 64 word \<Rightarrow> 64 word llM\<close> where
  \<open>nth_fst_impl = (\<lambda>al i. 
        let (a,_) = al in array_nth (array_of_arl a) i
      )\<close>

(*I thought this would just work out of the box with sepref*)
thm al_nth_hnr_mop[to_hnr]
  
lemma exists_eq_star_conv': "(\<lambda>s. (\<exists>x. (\<up>(k = x) \<and>* F x) s)) = F k"
  by (auto simp: sep_algebra_simps sep_conj_def pred_lift_extract_simps)

lemma the_pure_eq_Id: \<open>the_pure (\<lambda>(a::'a) c. \<up>(c = a)) = Id\<close>
proof -
  have \<open>the_pure (\<lambda>(a::'a) c. \<up>(c = a)) = the_pure (pure Id)\<close>
    by (auto simp: pure_def)
  from this[unfolded the_pure_pure] show ?thesis .
qed

lemma [sepref_fr_rules]:
  \<open>(uncurry nth_fst_impl, uncurry (RETURN oo nth_fst))
   \<in> [\<lambda>(a,i). i < length (fst a)]\<^sub>a sbi_aux_assn\<^sup>k *\<^sub>a snat_assn\<^sup>k \<rightarrow> word_assn\<close>
  unfolding nth_fst_impl_def nth_fst_def arl_nth_def al_assn_def hr_comp_def
  apply sepref_to_hoare
  apply vcg_all 
  subgoal for b bi a ba aa ab bb bc asf s x
    apply (auto)
    apply (rule vcg_framed_erules(129))
    apply assumption+
    apply (subgoal_tac
          \<open>PRECOND
                  (FRAME (\<upharpoonleft>arl_assn x (aa, ab, bb))
                  (\<upharpoonleft>arl_assn x (aa, ab, bb)  \<and>*
                  \<upharpoonleft>snat.assn b bi \<and>*
                  \<up>(b < length x))
                  (\<upharpoonleft>snat.assn b bi \<and>*
                  \<up>(b < length x) \<and>*
                  \<up>((x, a) \<in> \<langle>the_pure (\<lambda>a c. \<up>(c = a))\<rangle>list_rel))
          )\<close>)
    apply assumption
    subgoal
      by (auto simp: STATE_def PRECOND_def FRAME_def snat_rel_def snat.rel_def
          br_def list_rel_imp_same_length snat.assn_def pure_true_conv)
    subgoal
      apply (auto simp: exists_eq_star_conv' pure_true_conv)
      apply (auto simp: PRECOND_def EXTRACT_def POSTCOND_def 
             list_rel_imp_same_length snat.assn_def pure_true_conv)
      apply (rule STATE_monoI)
      apply assumption
      apply (auto simp: entails_def sep_conj_def)
      apply (rule_tac x=xa in exI)
      apply (rule_tac x=\<open>xaa + ya\<close> in exI)
      apply (auto simp: )
      apply (rule_tac x=x in exI)
      apply (rule_tac x=xa in exI)
      apply (rule_tac x=0 in exI)
      apply (auto simp: pure_true_conv)
      apply (drule param_nth[of b _ b])
      apply (auto simp: pure_true_conv)
      apply (auto simp: the_pure_eq_Id)
      by (simp add: pred_lift_extract_simps(1))
    done
  done

lemma [llvm_code,llvm_inline]: \<open>nth_fst_impl = (\<lambda>al i. 
        let (x,_) = al in arl_nth x i
      )\<close>
  unfolding nth_fst_impl_def arl_nth_def array_of_arl_def by auto

definition get_or_zero_fst where
  \<open>get_or_zero_fst a b = get_or_zero (fst a) b\<close>

lemma get_or_zero_fst_alt_def:
  "get_or_zero_fst ai i \<equiv> if i < length (fst ai) then fst ai ! i else 0"
  unfolding get_or_zero_fst_def get_or_zero_def
  by auto

(*
export_llvm nth_fst_impl file "/tmp/test.ll"
*)
sepref_def get_or_zero_fst_impl
  is \<open>uncurry (RETURN \<circ>\<circ> get_or_zero_fst)\<close>
  :: \<open>sbi_aux_assn\<^sup>k  *\<^sub>a (snat_assn' TYPE(64))\<^sup>k  \<rightarrow>\<^sub>a word_assn' TYPE(64)\<close>
  unfolding get_or_zero_fst_alt_def length_fst_def[symmetric]
    nth_fst_def[symmetric]
  supply [simp] = length_fst_def
  by sepref

definition signed_big_int_inv :: "signed_big_int \<Rightarrow> signed_big_int" where
  "signed_big_int_inv ai = (let (lsa,\<sigma>\<^sub>a) = ai in (lsa, \<not>\<sigma>\<^sub>a))"

definition signed_big_int_inv_impl :: "(64 word \<times> 64 word \<times> 64 word ptr) \<times> 1 word \<Rightarrow> ((64 word \<times> 64 word \<times> 64 word ptr) \<times> 1 word) llM" where
  "signed_big_int_inv_impl = (\<lambda>ai.
    let (ls\<^sub>a,\<sigma>\<^sub>a) = ai ; (l,c,a) = ls\<^sub>a in doM{
      \<sigma>\<^sub>a_inv \<leftarrow> ll_add \<sigma>\<^sub>a 1;
      Mreturn ((l,c,a),\<sigma>\<^sub>a_inv)
    }
  )"
lemma signed_big_int_inv_impl_refine[sepref_fr_rules]:
  "(signed_big_int_inv_impl, RETURN o signed_big_int_inv) \<in> sbi_aux_assn\<^sup>k \<rightarrow>\<^sub>a sbi_aux_assn"
  unfolding signed_big_int_inv_def signed_big_int_inv_impl_def
  apply sepref_to_hoare
  apply vcg_all
  oops
  (* Not sure if we will even need subtraction, so i stop here for now *)


end
