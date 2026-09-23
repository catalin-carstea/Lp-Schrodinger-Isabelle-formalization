theory Inverse_Schrodinger_Lp_Qstar_Annular_I1_Envelope
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_009.Inverse_Schrodinger_Lp_Qstar_Localized_Holder"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Annular_Kernel_Integral_Bounds"
begin

section \<open>Amplitude-weighted envelope for the first annular term\<close>

definition slp_qstar_annular_I1_integrand ::
  "real \<Rightarrow> slp_scalar_field \<Rightarrow> slp_point \<Rightarrow>
    slp_point \<Rightarrow> real"
where
  "slp_qstar_annular_I1_integrand delta f z y =
    slp_annular_I1_integrand delta z y * norm (f y)"

definition slp_qstar_annular_I1_potential ::
  "real \<Rightarrow> slp_scalar_field \<Rightarrow> slp_point \<Rightarrow> real"
where
  "slp_qstar_annular_I1_potential delta f z =
    integral\<^sup>L lborel (slp_qstar_annular_I1_integrand delta f z)"

theorem slp_qstar_annular_I1_envelope:
  assumes exponent_lower: "1 < a"
    and exponent_upper: "a < 2"
    and delta_positive: "0 < delta"
    and amplitude_lp:
      "aim_complex_lp_on_plane (aim_hls_target_exponent a) f"
  shows integrand_measurable:
      "slp_qstar_annular_I1_integrand delta f z
        \<in> borel_measurable lborel"
    and integrand_integrable:
      "integrable lborel (slp_qstar_annular_I1_integrand delta f z)"
    and potential_nonnegative:
      "0 \<le> slp_qstar_annular_I1_potential delta f z"
    and potential_bound:
      "slp_qstar_annular_I1_potential delta f z \<le>
        (1 / delta) * slp_localized_riesz_potential delta f z"
    and potential_outside:
      "z \<notin> cball 0 (3 * delta) \<Longrightarrow>
        slp_qstar_annular_I1_potential delta f z = 0"
proof -
  have amplitude_measurable: "f \<in> borel_measurable lborel"
    using amplitude_lp unfolding aim_complex_lp_on_plane_def by blast
  have weighted_measurable:
      "slp_qstar_annular_I1_integrand delta f z
        \<in> borel_measurable lborel"
    unfolding slp_qstar_annular_I1_integrand_def
    using amplitude_measurable by measurable
  show "slp_qstar_annular_I1_integrand delta f z
      \<in> borel_measurable lborel"
    by (rule weighted_measurable)
  have localized_integrable:
      "integrable lborel (slp_localized_riesz_integrand delta f z)"
    by (rule slp_qstar_localized_riesz_holder(1)[OF exponent_lower
          exponent_upper delta_positive amplitude_lp])
  let ?majorant =
    "\<lambda>y. (1 / delta) * slp_localized_riesz_integrand delta f z y"
  have majorant_integrable: "integrable lborel ?majorant"
    using localized_integrable by simp
  have pointwise_majorant:
      "slp_qstar_annular_I1_integrand delta f z y \<le> ?majorant y" for y
  proof -
    have raw_bound:
        "slp_annular_I1_integrand delta z y \<le>
          (1 / delta) * slp_localized_cauchy_kernel delta (z - y)"
      by (rule slp_annular_I1_pointwise_majorant[OF delta_positive])
    have multiplied:
        "slp_annular_I1_integrand delta z y * norm (f y) \<le>
          ((1 / delta) *
            slp_localized_cauchy_kernel delta (z - y)) * norm (f y)"
      by (rule mult_right_mono[OF raw_bound norm_ge_zero])
    show ?thesis
      using multiplied
      by (simp only: slp_qstar_annular_I1_integrand_def
          slp_localized_riesz_integrand_def mult.assoc)
  qed
  have weighted_nonnegative:
      "0 \<le> slp_qstar_annular_I1_integrand delta f z y" for y
    unfolding slp_qstar_annular_I1_integrand_def
    by (rule mult_nonneg_nonneg)
      (rule slp_annular_I1_integrand_nonnegative, rule norm_ge_zero)
  have majorant_nonnegative: "0 \<le> ?majorant y" for y
    using delta_positive slp_localized_riesz_integrand_nonnegative[of
      delta f z y] by simp
  have weighted_integrable:
      "integrable lborel (slp_qstar_annular_I1_integrand delta f z)"
  proof (rule Bochner_Integration.integrable_bound[OF majorant_integrable
        weighted_measurable])
    show "AE y in lborel.
        norm (slp_qstar_annular_I1_integrand delta f z y) \<le>
          norm (?majorant y)"
    proof (rule AE_I2)
      fix y :: slp_point
      have weighted_norm:
          "norm (slp_qstar_annular_I1_integrand delta f z y) =
            slp_qstar_annular_I1_integrand delta f z y"
        using weighted_nonnegative[of y] by simp
      have majorant_norm: "norm (?majorant y) = ?majorant y"
        using delta_positive
          slp_localized_riesz_integrand_nonnegative[of delta f z y]
        by simp
      show "norm (slp_qstar_annular_I1_integrand delta f z y) \<le>
          norm (?majorant y)"
        using pointwise_majorant[of y] weighted_norm majorant_norm by simp
    qed
  qed
  show "integrable lborel (slp_qstar_annular_I1_integrand delta f z)"
    by (rule weighted_integrable)
  show "0 \<le> slp_qstar_annular_I1_potential delta f z"
    unfolding slp_qstar_annular_I1_potential_def
    by (rule integral_nonneg_AE) (simp add: weighted_nonnegative)
  have integral_bound:
      "integral\<^sup>L lborel
          (slp_qstar_annular_I1_integrand delta f z) \<le>
        integral\<^sup>L lborel ?majorant"
    by (rule Bochner_Integration.integral_mono[OF weighted_integrable
          majorant_integrable])
      (use pointwise_majorant in auto)
  have majorant_integral:
      "integral\<^sup>L lborel ?majorant =
        (1 / delta) * slp_localized_riesz_potential delta f z"
    unfolding slp_localized_riesz_potential_def
    using localized_integrable by simp
  show "slp_qstar_annular_I1_potential delta f z \<le>
      (1 / delta) * slp_localized_riesz_potential delta f z"
    unfolding slp_qstar_annular_I1_potential_def
    using integral_bound majorant_integral by linarith
  assume outside: "z \<notin> cball 0 (3 * delta)"
  have output_large: "3 * delta < norm z"
    using outside delta_positive by simp
  have integrand_zero:
      "slp_qstar_annular_I1_integrand delta f z y = 0" for y
  proof -
    have not_carrier:
        "\<not> (delta \<le> norm y \<and> norm y \<le> 2 * delta \<and>
          norm (z - y) \<le> delta)"
    proof
      assume carrier:
        "delta \<le> norm y \<and> norm y \<le> 2 * delta \<and>
          norm (z - y) \<le> delta"
      have triangle_raw:
          "norm ((z - y) + y) \<le> norm (z - y) + norm y"
        by (rule norm_triangle_ineq)
      have triangle: "norm z \<le> norm (z - y) + norm y"
        using triangle_raw by (simp only: diff_add_cancel)
      show False
        using output_large carrier triangle by linarith
    qed
    show ?thesis
    proof (cases "delta \<le> norm y \<and> norm y \<le> 2 * delta \<and>
        norm (z - y) \<le> delta")
      case True
      then show ?thesis
        using not_carrier by blast
    next
      case False
      show ?thesis
        by (simp add: slp_qstar_annular_I1_integrand_def
            slp_annular_I1_integrand_def False)
    qed
  qed
  have integrand_zero_function:
      "slp_qstar_annular_I1_integrand delta f z = (\<lambda>y. 0)"
    by (rule ext) (rule integrand_zero)
  show "slp_qstar_annular_I1_potential delta f z = 0"
    unfolding slp_qstar_annular_I1_potential_def
    by (simp add: integrand_zero_function)
qed

end
