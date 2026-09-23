theory Inverse_Schrodinger_Lp_Terminal_Weighted_Center_Average_Error
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Positive_Ennreal_Uniform_Difference"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Positive_Ennreal_Bounded_Support_L1"
begin

section \<open>Terminal-weighted center-average error\<close>

context aim_planar_riesz_hls
begin

theorem slp_positive_root_output_density_terminal_weighted_center_average_error_nn_integral_tendsto_zero:
  fixes R C p :: real
    and X :: "slp_point set"
    and cutoff potential phi :: "slp_point \<Rightarrow> complex"
    and n :: nat
  assumes radius_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and potential_outside: "\<And>x. x \<notin> X \<Longrightarrow> potential x = 0"
    and cutoff_bound: "\<And>x. cmod (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
    and phi_integrable: "integrable lborel phi"
    and uniform_convergence:
      "uniform_limit UNIV (\<lambda>tau. slp_center_average tau phi) phi at_top"
  shows
    "((\<lambda>tau. \<integral>\<^sup>+ output.
        slp_positive_root_output_density R cutoff potential
          (slp_positive_terminal_riesz_weight R potential) n potential output *
        ennreal (Real_Vector_Spaces.norm
          (slp_center_average tau phi output - phi output))
        \<partial>lborel) \<longlongrightarrow> 0) at_top"
proof -
  let ?q = "slp_branch_power_exponent p"
  let ?F = "\<lambda>output.
    slp_positive_root_output_density R cutoff potential
      (slp_positive_terminal_riesz_weight R potential) n potential output"
  note all_order =
    slp_positive_root_output_density_all_orders_terminal_weighted_lp_root[OF
      radius_nonnegative p_lower p_upper X_measurable X_bounded
      cutoff_measurable potential_lp potential_lp potential_outside
      cutoff_bound C_nonnegative]
  obtain L where F_lp: "slp_positive_ennreal_lp_on_plane ?q ?F"
    using all_order(2)[of n] by blast
  have F_finite: "AE output in lborel. ?F output < top_class.top"
    using F_lp unfolding slp_positive_ennreal_lp_on_plane_def by blast
  have F_real_integrable:
      "integrable lborel (\<lambda>output. enn2real (?F output))"
    by (rule
        slp_positive_root_output_density_terminal_weighted_real_integrable[OF
          radius_nonnegative p_lower p_upper X_measurable X_bounded
          cutoff_measurable potential_lp potential_outside cutoff_bound
          C_nonnegative])
  have phi_measurable: "phi \<in> borel_measurable lborel"
    using phi_integrable by measurable
  have average_measurable:
      "\<And>tau. slp_center_average tau phi \<in> borel_measurable lborel"
    by (rule slp_center_average_measurable[OF phi_integrable])
  show ?thesis
    by (rule
        slp_positive_ennreal_uniform_difference_nn_integral_tendsto_zero[OF
          F_finite F_real_integrable average_measurable phi_measurable
          uniform_convergence])
qed

end

end
