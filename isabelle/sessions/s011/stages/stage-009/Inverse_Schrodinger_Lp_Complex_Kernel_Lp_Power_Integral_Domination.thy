theory Inverse_Schrodinger_Lp_Complex_Kernel_Lp_Power_Integral_Domination
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_005.Inverse_Schrodinger_Lp_Complex_Kernel_Lp_Domination"
begin

section \<open>Quantitative power-integral domination for complex kernels\<close>

theorem slp_complex_kernel_power_integral_le_positive_density:
  fixes kernel :: "slp_point \<Rightarrow> complex"
    and density :: "slp_point \<Rightarrow> ennreal"
  assumes exponent_positive: "0 < s"
    and density_lp: "slp_positive_ennreal_lp_on_plane s density"
    and kernel_measurable: "kernel \<in> borel_measurable lborel"
    and dominated:
      "AE center in lborel.
        ennreal (norm_class.norm (kernel center)) \<le> density center"
  shows
    "integrable lborel
      (\<lambda>center. norm_class.norm (kernel center) powr s)"
    "integral\<^sup>L lborel
      (\<lambda>center. norm_class.norm (kernel center) powr s) \<le>
      integral\<^sup>L lborel (\<lambda>center. enn2real (density center) powr s)"
proof -
  have density_finite:
      "AE center in lborel. density center < top_class.top"
    and density_power_integrable:
      "integrable lborel (\<lambda>center. enn2real (density center) powr s)"
    using density_lp
    unfolding slp_positive_ennreal_lp_on_plane_def by blast+
  have kernel_lp:
      "slp_positive_ennreal_lp_on_plane s
        (\<lambda>center. ennreal (norm_class.norm (kernel center)))"
    by (rule slp_complex_kernel_lp_of_positive_density_domination[OF
          exponent_positive density_lp kernel_measurable dominated])
  have kernel_power_integrable:
      "integrable lborel
        (\<lambda>center. norm_class.norm (kernel center) powr s)"
    using kernel_lp
    unfolding slp_positive_ennreal_lp_on_plane_def by simp
  have power_dominated:
      "AE center in lborel.
        norm_class.norm (kernel center) powr s \<le>
          enn2real (density center) powr s"
    using dominated density_finite
  proof eventually_elim
    fix center :: slp_point
    assume pointwise:
        "ennreal (norm_class.norm (kernel center)) \<le> density center"
      and finite: "density center < top_class.top"
    have real_order:
        "norm_class.norm (kernel center) \<le> enn2real (density center)"
      using enn2real_mono[OF pointwise] finite by simp
    show "norm_class.norm (kernel center) powr s \<le>
        enn2real (density center) powr s"
      by (rule powr_mono2[OF less_imp_le[OF exponent_positive]])
        (use real_order in simp_all)
  qed
  show "integrable lborel
      (\<lambda>center. norm_class.norm (kernel center) powr s)"
    using kernel_power_integrable .
  show "integral\<^sup>L lborel
      (\<lambda>center. norm_class.norm (kernel center) powr s) \<le>
      integral\<^sup>L lborel (\<lambda>center. enn2real (density center) powr s)"
    by (rule integral_mono_AE[OF kernel_power_integrable
          density_power_integrable power_dominated])
qed

end
