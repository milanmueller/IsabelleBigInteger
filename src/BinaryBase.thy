theory BinaryBase
  imports BaseDecomp
begin

global_interpretation binary: base_decomp 2
  defines to_bin = "base_decomp.base_decomp 2"
     and bin_inv = "base_decomp.base_invar 2" 
     and bin_rel = "base_decomp.base_rel 2"
      and log2   = "base_decomp.digits 2"
  by unfold_locales (simp_all add:base_decomp_def)


term "to_bin" 
term "bin_rel"

definition bool_nat :: "bool \<Rightarrow> nat" where "bool_nat \<equiv> (\<lambda> b. if b then 1 else 0)"

definition bit_rel :: "(bool \<times> nat) set" where "bit_rel \<equiv> {(True, 1), (False, 0)}"



end