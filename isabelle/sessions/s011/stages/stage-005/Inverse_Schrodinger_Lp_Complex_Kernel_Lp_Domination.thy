theory Inverse_Schrodinger_Lp_Complex_Kernel_Lp_Domination
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_005.Inverse_Schrodinger_Lp_Positive_Ennreal_Lp_Domination"
begin

section \<open>Complex center kernels dominated by positive densities\<close>

theorem slp_complex_kernel_lp_of_positive_density_domination:
  fixes kernel :: "slp_point \<Rightarrow> complex"
    and density :: "slp_point \<Rightarrow> ennreal"
  assumes exponent_positive: "0 < s"
    and density_lp: "slp_positive_ennreal_lp_on_plane s density"
    and kernel_measurable: "kernel \<in> borel_measurable lborel"
    and dominated:
      "AE center in lborel.
        ennreal (norm_class.norm (kernel center)) \<le> density center"
  shows
    "slp_positive_ennreal_lp_on_plane s
      (\<lambda>center. ennreal (norm_class.norm (kernel center)))"
proof -
  have lifted_measurable:
      "(\<lambda>center. ennreal (norm_class.norm (kernel center)))
        \<in> borel_measurable lborel"
    using kernel_measurable by measurable
  show ?thesis
    by (rule slp_positive_ennreal_lp_mono_AE[OF exponent_positive density_lp
          lifted_measurable dominated])
qed

end
