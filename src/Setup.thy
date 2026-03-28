theory Setup
  imports Main "Isabelle_LLVM.IICF"
begin



subsubsection \<open>Min/Max\<close>  (* TODO: Move. Ideally upstream to IsabelleLLVM!*)
sepref_register min max

sepref_def min_unat_impl [llvm_inline] is "uncurry (RETURN oo min)" :: "(unat_assn' TYPE('l::len))\<^sup>k *\<^sub>a (unat_assn' TYPE('l::len))\<^sup>k \<rightarrow>\<^sub>a unat_assn' TYPE('l::len)"
  unfolding min_def by sepref

sepref_def max_unat_impl [llvm_inline] is "uncurry (RETURN oo max)" :: "(unat_assn' TYPE('l::len))\<^sup>k *\<^sub>a (unat_assn' TYPE('l::len))\<^sup>k \<rightarrow>\<^sub>a unat_assn' TYPE('l::len)"
  unfolding max_def by sepref

sepref_def min_snat_impl [llvm_inline] is "uncurry (RETURN oo min)" :: "(snat_assn' TYPE('l::len2))\<^sup>k *\<^sub>a (snat_assn' TYPE('l::len2))\<^sup>k \<rightarrow>\<^sub>a snat_assn' TYPE('l::len2)"
  unfolding min_def by sepref

sepref_def max_snat_impl [llvm_inline] is "uncurry (RETURN oo max)" :: "(snat_assn' TYPE('l::len2))\<^sup>k *\<^sub>a (snat_assn' TYPE('l::len2))\<^sup>k \<rightarrow>\<^sub>a snat_assn' TYPE('l::len2)"
  unfolding max_def by sepref
  
sepref_def min_sint_impl [llvm_inline] is "uncurry (RETURN oo min)" :: "(sint_assn' TYPE('l::len2))\<^sup>k *\<^sub>a (sint_assn' TYPE('l::len2))\<^sup>k \<rightarrow>\<^sub>a sint_assn' TYPE('l::len2)"
  unfolding min_def by sepref

sepref_def max_sint_impl [llvm_inline] is "uncurry (RETURN oo max)" :: "(sint_assn' TYPE('l::len2))\<^sup>k *\<^sub>a (sint_assn' TYPE('l::len2))\<^sup>k \<rightarrow>\<^sub>a sint_assn' TYPE('l::len2)"
  unfolding max_def by sepref



subsubsection \<open>Refine_Transfer: fixes\<close>

(*
  TODO: Change in RefineG_While! Double-check that transfer is actually only used for code generation.
    Otherwise, the invar-preserving variants may make sense, too!

*)
context transfer_WHILE begin

  lemmas [refine_transfer del] = transfer_WHILEIT

  lemma transfer_WHILEIT_fixed[refine_transfer]:
    assumes REF: "\<And>x. \<alpha> (f x) \<le> F x"
    shows "\<alpha> (cWHILET b f x) \<le> aWHILEIT I b F x"
    unfolding c.WHILET_def c.WHILEIT_def a.WHILEIT_def
    apply (rule transfer_RECT[OF _ c.WHILEI_body_trimono])
    unfolding WHILEI_body_def
    apply auto
    apply (rule transfer_bind)
    apply (rule REF)
    apply assumption
    apply (rule transfer_return)
    done

  lemmas [refine_transfer del] = transfer_WHILEI
  
  lemma transfer_WHILEI_fixed[refine_transfer]:
    assumes REF: "\<And>x. \<alpha> (f x) \<le> F x"
    shows "\<alpha> (cWHILE b f x) \<le> aWHILEI I b F x"
    unfolding c.WHILEI_def c.WHILE_def a.WHILEI_def
    apply (rule transfer_REC[OF _ c.WHILEI_body_trimono])
    unfolding WHILEI_body_def
    apply auto
    apply (rule transfer_bind)
    apply (rule REF)
    apply assumption
    apply (rule transfer_return)
    done
    


end


subsubsection \<open>Codegen Setup\<close>

lemma gen_code_thm_refg_fixp:
	fixes x
	assumes D: "f \<equiv> RECT B"
	assumes M: "trimono B"
	shows "f x \<equiv> B f x"
	unfolding D 
	using RECT_unfold[OF M] by simp
	
declaration \<open>K (Definition_Utils.declare_extraction_group @{binding refg} #> snd)\<close>
	
declaration \<open> fn _ =>
	Definition_Utils.add_extraction ("refg",\<^here>) {
		pattern = Logic.varify_global @{term "RECT x"},
		gen_thm = @{thm gen_code_thm_refg_fixp},
		gen_tac =  Refine_Mono_Prover.untriggered_mono_tac
	}
\<close>


end