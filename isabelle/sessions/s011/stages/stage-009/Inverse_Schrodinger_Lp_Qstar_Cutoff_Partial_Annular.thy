theory Inverse_Schrodinger_Lp_Qstar_Cutoff_Partial_Annular
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_009.Inverse_Schrodinger_Lp_Qstar_Cutoff_Partial_Support"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_009.Inverse_Schrodinger_Lp_Smooth_Cutoff_Profile"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_009.Inverse_Schrodinger_Lp_Qstar_Annular_I2_Riesz_HLS"
begin

section \<open>Pointwise annular domination of the cutoff-derivative term\<close>

definition slp_qstar_cutoff_partial_integrand ::
  "real \<Rightarrow> slp_scalar_field \<Rightarrow> slp_point \<Rightarrow>
    slp_point \<Rightarrow> complex"
where
  "slp_qstar_cutoff_partial_integrand delta f z y =
    slp_cauchy_kernel SLP_Partial_Inverse z y *
      slp_real_wirtinger_partial
        (slp_global_cutoff.slp_scaled_cutoff_derivative delta 0 y) *
      inverse (slp_point_as_complex y) * f y"

theorem slp_qstar_cutoff_partial_integrand_le_annular:
  assumes delta_positive: "0 < delta"
  shows
    "norm (slp_qstar_cutoff_partial_integrand delta f z y) \<le>
      (slp_global_cutoff_L / delta) *
        (slp_qstar_annular_I1_integrand delta f z y +
         slp_qstar_annular_I2_weighted_integrand delta f z y)"
proof -
  let ?D = "slp_real_wirtinger_partial
    (slp_global_cutoff.slp_scaled_cutoff_derivative delta 0 y)"
  let ?B = "slp_radial_inverse (z - y) *
    slp_radial_inverse y * norm (f y)"
  have partial_bound:
      "norm ?D \<le> slp_global_cutoff_L / delta"
    by (rule slp_global_cutoff.slp_scaled_cutoff_partial_bound[OF
          delta_positive])
  have coefficient_nonnegative:
      "0 \<le> slp_global_cutoff_L / delta"
    by (rule order_trans[OF norm_ge_zero partial_bound])
  have base_nonnegative: "0 \<le> ?B"
    by (intro mult_nonneg_nonneg slp_radial_inverse_nonnegative norm_ge_zero)
  have I1_nonnegative:
      "0 \<le> slp_qstar_annular_I1_integrand delta f z y"
    unfolding slp_qstar_annular_I1_integrand_def by simp
  have I2_nonnegative:
      "0 \<le> slp_qstar_annular_I2_weighted_integrand delta f z y"
    by (rule slp_qstar_annular_I2_weighted_integrand_nonnegative)
  show ?thesis
  proof (cases "?D = 0")
    case True
    have integrand_zero:
        "slp_qstar_cutoff_partial_integrand delta f z y = 0"
      unfolding slp_qstar_cutoff_partial_integrand_def True
      by (simp only: mult_zero_right mult_zero_left)
    have carrier_sum_nonnegative:
        "0 \<le> slp_qstar_annular_I1_integrand delta f z y +
          slp_qstar_annular_I2_weighted_integrand delta f z y"
      using I1_nonnegative I2_nonnegative by linarith
    have right_nonnegative:
        "0 \<le> (slp_global_cutoff_L / delta) *
          (slp_qstar_annular_I1_integrand delta f z y +
           slp_qstar_annular_I2_weighted_integrand delta f z y)"
      by (rule mult_nonneg_nonneg[OF coefficient_nonnegative
            carrier_sum_nonnegative])
    show ?thesis
      unfolding integrand_zero norm_zero
      by (rule right_nonnegative)
  next
    case False
    have annulus:
        "delta \<le> norm y \<and> norm y \<le> 2 * delta"
      using slp_cutoff_profile.slp_scaled_cutoff_partial_support[OF
          slp_global_cutoff_profile_spec[THEN conjunct1]
          delta_positive False]
      by simp
    have norm_value:
        "norm (slp_qstar_cutoff_partial_integrand delta f z y) =
          norm ?D * ?B"
      unfolding slp_qstar_cutoff_partial_integrand_def
        slp_radial_inverse_def
      by (simp only: norm_mult slp_cauchy_kernel_norm norm_inverse
          slp_point_as_complex_norm slp_radial_inverse_def
          mult.assoc mult.commute mult.left_commute)
    have norm_to_base:
        "norm (slp_qstar_cutoff_partial_integrand delta f z y) \<le>
          (slp_global_cutoff_L / delta) * ?B"
    proof -
      have "norm ?D * ?B \<le> (slp_global_cutoff_L / delta) * ?B"
        by (rule mult_right_mono[OF partial_bound base_nonnegative])
      then show ?thesis
        using norm_value by simp
    qed
    have base_to_carriers:
        "?B \<le>
          slp_qstar_annular_I1_integrand delta f z y +
          slp_qstar_annular_I2_weighted_integrand delta f z y"
    proof (cases "norm (z - y) \<le> delta")
      case True
      have near_carrier:
          "delta \<le> norm y \<and> norm y \<le> 2 * delta \<and>
            norm (z - y) \<le> delta"
        using annulus True by blast
      have I1_value:
          "slp_qstar_annular_I1_integrand delta f z y = ?B"
        unfolding slp_qstar_annular_I1_integrand_def
          slp_annular_I1_integrand_def if_P[OF near_carrier]
        by (rule refl)
      show ?thesis
        using I1_value I2_nonnegative by linarith
    next
      case False
      have far: "delta \<le> norm (z - y)"
        using False by simp
      have far_carrier:
          "delta \<le> norm y \<and> norm y \<le> 2 * delta \<and>
            delta \<le> norm (z - y)"
        using annulus far by blast
      have I2_value:
          "slp_qstar_annular_I2_weighted_integrand delta f z y = ?B"
        unfolding slp_qstar_annular_I2_weighted_integrand_def
          slp_annular_I2_integrand_def if_P[OF far_carrier]
        by (rule refl)
      show ?thesis
        using I2_value I1_nonnegative by linarith
    qed
    have scaled_base_to_carriers:
        "(slp_global_cutoff_L / delta) * ?B \<le>
          (slp_global_cutoff_L / delta) *
            (slp_qstar_annular_I1_integrand delta f z y +
             slp_qstar_annular_I2_weighted_integrand delta f z y)"
      by (rule mult_left_mono[OF base_to_carriers coefficient_nonnegative])
    show ?thesis
      by (rule order_trans[OF norm_to_base scaled_base_to_carriers])
  qed
qed

end
