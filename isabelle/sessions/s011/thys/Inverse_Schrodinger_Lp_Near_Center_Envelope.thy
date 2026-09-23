theory Inverse_Schrodinger_Lp_Near_Center_Envelope
  imports Inverse_Schrodinger_Lp_Annular_Kernel_Integral_Bounds
begin

section \<open>The near-center positive envelope\<close>

lemma slp_localized_riesz_integrable_of_uniform_bound:
  assumes f_measurable: "f \<in> borel_measurable lborel"
    and M_nonnegative: "0 \<le> M"
    and f_bound: "\<And>y. norm (f y) \<le> M"
  shows "integrable lborel (slp_localized_riesz_integrand R f z)"
proof -
  let ?majorant = "\<lambda>y. M * slp_localized_cauchy_kernel R (z - y)"
  have kernel_integrable:
    "integrable lborel (\<lambda>y. slp_localized_cauchy_kernel R (z - y))"
    by (rule slp_localized_cauchy_kernel_translate_integrable)
  have majorant_integrable: "integrable lborel ?majorant"
    using kernel_integrable by (rule integrable_mult_right)
  show ?thesis
  proof (rule Bochner_Integration.integrable_bound[OF majorant_integrable])
    show "slp_localized_riesz_integrand R f z
        \<in> borel_measurable lborel"
      by (rule slp_localized_riesz_integrand_measurable[OF f_measurable])
    show "AE y in lborel.
        norm (slp_localized_riesz_integrand R f z y) \<le>
          norm (?majorant y)"
    proof (rule AE_I2)
      fix y :: slp_point
      have kernel_nonnegative:
        "0 \<le> slp_localized_cauchy_kernel R (z - y)"
        by (rule slp_localized_cauchy_kernel_nonnegative)
      have domination:
        "slp_localized_riesz_integrand R f z y \<le> ?majorant y"
        unfolding slp_localized_riesz_integrand_def
        using mult_left_mono[OF f_bound[of y] kernel_nonnegative]
        by (simp add: mult.commute)
      have integrand_norm:
        "norm (slp_localized_riesz_integrand R f z y) =
          slp_localized_riesz_integrand R f z y"
        by (simp add: slp_localized_riesz_integrand_nonnegative)
      have majorant_norm: "norm (?majorant y) = ?majorant y"
        using M_nonnegative kernel_nonnegative by simp
      show "norm (slp_localized_riesz_integrand R f z y) \<le>
          norm (?majorant y)"
        using domination integrand_norm majorant_norm by linarith
    qed
  qed
qed

lemma slp_localized_riesz_potential_uniform_bound:
  assumes f_measurable: "f \<in> borel_measurable lborel"
    and M_nonnegative: "0 \<le> M"
    and f_bound: "\<And>y. norm (f y) \<le> M"
  shows "slp_localized_riesz_potential R f z \<le>
    M * integral\<^sup>L lborel (slp_localized_cauchy_kernel R)"
proof -
  let ?majorant = "\<lambda>y. M * slp_localized_cauchy_kernel R (z - y)"
  have integrand_integrable:
    "integrable lborel (slp_localized_riesz_integrand R f z)"
    by (rule slp_localized_riesz_integrable_of_uniform_bound[
          OF f_measurable M_nonnegative f_bound])
  have kernel_integrable:
    "integrable lborel (\<lambda>y. slp_localized_cauchy_kernel R (z - y))"
    by (rule slp_localized_cauchy_kernel_translate_integrable)
  have majorant_integrable: "integrable lborel ?majorant"
    using kernel_integrable by (rule integrable_mult_right)
  have bound:
    "integral\<^sup>L lborel (slp_localized_riesz_integrand R f z) \<le>
      integral\<^sup>L lborel ?majorant"
  proof (rule Bochner_Integration.integral_mono[OF integrand_integrable
        majorant_integrable])
    fix y :: slp_point
    assume "y \<in> space lborel"
    have kernel_nonnegative:
      "0 \<le> slp_localized_cauchy_kernel R (z - y)"
      by (rule slp_localized_cauchy_kernel_nonnegative)
    show "slp_localized_riesz_integrand R f z y \<le> ?majorant y"
      unfolding slp_localized_riesz_integrand_def
      using mult_left_mono[OF f_bound[of y] kernel_nonnegative]
      by (simp add: mult.commute)
  qed
  have translated:
    "integral\<^sup>L lborel
        (\<lambda>y. slp_localized_cauchy_kernel R (z - y)) =
      integral\<^sup>L lborel (slp_localized_cauchy_kernel R)"
    by (rule slp_localized_cauchy_kernel_reflected_translate_integral)
  have majorant_integral:
    "integral\<^sup>L lborel ?majorant =
      M * integral\<^sup>L lborel (slp_localized_cauchy_kernel R)"
    using kernel_integrable translated by simp
  show ?thesis
    unfolding slp_localized_riesz_potential_def
    using bound majorant_integral by linarith
qed

lemma slp_near_center_envelope_bound:
  assumes delta_positive: "0 < delta"
    and f_measurable: "f \<in> borel_measurable lborel"
    and M_nonnegative: "0 \<le> M"
    and f_bound: "\<And>y. norm (f y) \<le> M"
  shows "slp_localized_riesz_potential (2 * delta) f z \<le>
    2 * delta * M *
      integral\<^sup>L lborel (slp_localized_cauchy_kernel 1)"
proof -
  have envelope:
    "slp_localized_riesz_potential (2 * delta) f z \<le>
      M * integral\<^sup>L lborel
        (slp_localized_cauchy_kernel (2 * delta))"
    by (rule slp_localized_riesz_potential_uniform_bound[
          OF f_measurable M_nonnegative f_bound])
  have scaling:
    "integral\<^sup>L lborel (slp_localized_cauchy_kernel (2 * delta)) =
      (2 * delta) *
        integral\<^sup>L lborel (slp_localized_cauchy_kernel 1)"
    by (rule slp_localized_cauchy_kernel_integral_scale)
      (use delta_positive in simp)
  show ?thesis
    using envelope scaling by (simp add: algebra_simps)
qed

end
