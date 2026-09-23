theory Inverse_Schrodinger_Lp_Born_All_Order_Terminal_Lp
  imports Inverse_Schrodinger_Lp_Born_Zero_Uniform_Power
begin

section \<open>All-order positive branch control from terminal data\<close>

context aim_planar_riesz_hls
begin

theorem slp_positive_output_density_all_orders_from_terminal_lp:
  fixes R C p a b gamma r :: real
    and cutoff potential :: "slp_point \<Rightarrow> complex"
    and terminal_weight :: "slp_point \<Rightarrow> ennreal"
  assumes radius_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and a_lower: "1 < a"
    and b_lower: "1 < b"
    and conjugate: "1 / a + 1 / b = 1"
    and gamma_lower: "1 \<le> gamma"
    and gamma_upper: "gamma < 2"
    and gamma_scale: "1 < gamma / a"
    and r_scale: "1 < r / a"
    and conjugate_scales: "1 / (gamma / a) + 1 / (r / a) = 1"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and terminal_lp:
      "slp_positive_ennreal_lp_on_plane r terminal_weight"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
  shows "\<And>n. \<exists>L. 0 \<le> L \<and>
    (\<forall>origin. slp_positive_ennreal_lp_on_plane a
      (slp_positive_output_density R cutoff potential terminal_weight n
        origin)) \<and>
    (\<forall>origin. integral\<^sup>L lborel
      (\<lambda>output.
        enn2real
          (slp_positive_output_density R cutoff potential terminal_weight n
            origin output) powr a) \<le> L)"
proof -
  let ?L0 =
    "(inverse pi * C) powr a *
      (integral\<^sup>L lborel
          (\<lambda>x. abs (slp_localized_cauchy_kernel R x) powr gamma) /
          (gamma / a) +
        integral\<^sup>L lborel
          (\<lambda>x. enn2real (terminal_weight x) powr r) / (r / a))"
  have terminal_weight_measurable:
      "terminal_weight \<in> borel_measurable lborel"
    using terminal_lp unfolding slp_positive_ennreal_lp_on_plane_def by blast
  have terminal_power_integrable:
      "integrable lborel
        (\<lambda>x. enn2real (terminal_weight x) powr r)"
    using terminal_lp unfolding slp_positive_ennreal_lp_on_plane_def by blast
  have kernel_power_integrable:
      "integrable lborel
        (\<lambda>x. abs (slp_localized_cauchy_kernel R x) powr gamma)"
    by (rule slp_localized_cauchy_kernel_power_integrable[
          OF gamma_lower gamma_upper])
  have kernel_integral_nonnegative:
      "0 \<le> integral\<^sup>L lborel
        (\<lambda>x. abs (slp_localized_cauchy_kernel R x) powr gamma)"
    by (rule integral_nonneg_AE) simp
  have terminal_integral_nonnegative:
      "0 \<le> integral\<^sup>L lborel
        (\<lambda>x. enn2real (terminal_weight x) powr r)"
    by (rule integral_nonneg_AE) simp
  have gamma_scale_positive: "0 < gamma / a"
    using gamma_scale by linarith
  have r_scale_positive: "0 < r / a"
    using r_scale by linarith
  have kernel_term_nonnegative:
      "0 \<le> integral\<^sup>L lborel
          (\<lambda>x. abs (slp_localized_cauchy_kernel R x) powr gamma) /
          (gamma / a)"
    by (rule divide_nonneg_pos)
      (use kernel_integral_nonnegative gamma_scale_positive in simp_all)
  have terminal_term_nonnegative:
      "0 \<le> integral\<^sup>L lborel
          (\<lambda>x. enn2real (terminal_weight x) powr r) / (r / a)"
    by (rule divide_nonneg_pos)
      (use terminal_integral_nonnegative r_scale_positive in simp_all)
  have L0_nonnegative: "0 \<le> ?L0"
    using kernel_term_nonnegative terminal_term_nonnegative by simp
  have base_lp:
      "\<And>origin. slp_positive_ennreal_lp_on_plane a
        (slp_positive_output_density R cutoff potential terminal_weight 0
          origin)"
    by (rule slp_positive_output_density_zero_uniform_power(1)[OF
          _ gamma_lower gamma_upper gamma_scale r_scale conjugate_scales
          terminal_lp cutoff_measurable cutoff_bound C_nonnegative])
      (use a_lower in linarith)
  have base_power_bound:
      "\<And>origin. integral\<^sup>L lborel
        (\<lambda>output.
          enn2real
            (slp_positive_output_density R cutoff potential terminal_weight 0
              origin output) powr a) \<le> ?L0"
    by (rule slp_positive_output_density_zero_uniform_power(2)[OF
          _ gamma_lower gamma_upper gamma_scale r_scale conjugate_scales
          terminal_lp cutoff_measurable cutoff_bound C_nonnegative])
      (use a_lower in linarith)
  obtain B where B_nonnegative: "0 \<le> B"
    and block_mass_bound:
      "\<forall>origin.
        integral\<^sup>L lborel
          (slp_positive_branch_block_weight_real R cutoff potential origin)
          \<le> B"
    using slp_positive_branch_block_weight_real_uniform[OF
      radius_nonnegative p_lower p_upper cutoff_measurable potential_lp
      cutoff_bound C_nonnegative] by blast
  show "\<exists>L. 0 \<le> L \<and>
      (\<forall>origin. slp_positive_ennreal_lp_on_plane a
        (slp_positive_output_density R cutoff potential terminal_weight n
          origin)) \<and>
      (\<forall>origin. integral\<^sup>L lborel
        (\<lambda>output.
          enn2real
            (slp_positive_output_density R cutoff potential terminal_weight n
              origin output) powr a) \<le> L)"
    for n
    by (rule slp_positive_output_density_all_orders_uniform_power[OF
          radius_nonnegative p_lower p_upper a_lower b_lower conjugate
          cutoff_measurable potential_lp terminal_weight_measurable
          cutoff_bound base_lp base_power_bound L0_nonnegative
          block_mass_bound[rule_format] B_nonnegative])
qed

end

end
