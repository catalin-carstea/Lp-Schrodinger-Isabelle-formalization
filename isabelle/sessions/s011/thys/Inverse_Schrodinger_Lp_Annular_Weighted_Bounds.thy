theory Inverse_Schrodinger_Lp_Annular_Weighted_Bounds
  imports Inverse_Schrodinger_Lp_Near_Center_Envelope
begin

section \<open>Weighted bounds for the checked annular pieces\<close>

lemma slp_annular_I_sum_integral_bound:
  assumes delta_positive: "0 < delta"
  shows "integral\<^sup>L lborel (slp_annular_I1_integrand delta z) +
      integral\<^sup>L lborel (slp_annular_I2_integrand delta z) \<le>
    3 * integral\<^sup>L lborel (slp_localized_cauchy_kernel 1)"
  using slp_annular_I1_integral_bound[OF delta_positive, of z]
    slp_annular_I2_integral_bound[OF delta_positive, of z]
  by linarith

lemma slp_cutoff_annular_weighted_bound:
  assumes delta_positive: "0 < delta"
    and L_nonnegative: "0 \<le> L"
    and M_nonnegative: "0 \<le> M"
  shows "(L / delta) * M *
      (integral\<^sup>L lborel (slp_annular_I1_integrand delta z) +
        integral\<^sup>L lborel (slp_annular_I2_integrand delta z)) \<le>
    (3 * L * M / delta) *
      integral\<^sup>L lborel (slp_localized_cauchy_kernel 1)"
proof -
  have coefficient_nonnegative: "0 \<le> (L / delta) * M"
    using delta_positive L_nonnegative M_nonnegative by simp
  have weighted:
    "(L / delta) * M *
        (integral\<^sup>L lborel (slp_annular_I1_integrand delta z) +
          integral\<^sup>L lborel (slp_annular_I2_integrand delta z)) \<le>
      (L / delta) * M *
        (3 * integral\<^sup>L lborel (slp_localized_cauchy_kernel 1))"
    by (rule mult_left_mono[OF
          slp_annular_I_sum_integral_bound[OF delta_positive]
          coefficient_nonnegative])
  show ?thesis
    using weighted by (simp add: algebra_simps)
qed

lemma slp_J1_amplitude_weighted_bound:
  assumes delta_positive: "0 < delta"
    and M_nonnegative: "0 \<le> M"
  shows "M * integral\<^sup>L lborel (slp_annular_J1_integrand delta z) \<le>
    (M / delta) *
      integral\<^sup>L lborel (slp_localized_cauchy_kernel 1)"
proof -
  have weighted:
    "M * integral\<^sup>L lborel (slp_annular_J1_integrand delta z) \<le>
      M * ((1 / delta) *
        integral\<^sup>L lborel (slp_localized_cauchy_kernel 1))"
    by (rule mult_left_mono[OF
          slp_annular_J1_integral_bound[OF delta_positive]
          M_nonnegative])
  show ?thesis
    using weighted by (simp add: algebra_simps)
qed

lemma slp_checked_annular_weighted_sum_bound:
  assumes delta_positive: "0 < delta"
    and L_nonnegative: "0 \<le> L"
    and M_nonnegative: "0 \<le> M"
  shows "(L / delta) * M *
        (integral\<^sup>L lborel (slp_annular_I1_integrand delta z) +
          integral\<^sup>L lborel (slp_annular_I2_integrand delta z)) +
      M * integral\<^sup>L lborel (slp_annular_J1_integrand delta z) \<le>
    ((3 * L + 1) * M / delta) *
      integral\<^sup>L lborel (slp_localized_cauchy_kernel 1)"
proof -
  have cutoff:
    "(L / delta) * M *
        (integral\<^sup>L lborel (slp_annular_I1_integrand delta z) +
          integral\<^sup>L lborel (slp_annular_I2_integrand delta z)) \<le>
      (3 * L * M / delta) *
        integral\<^sup>L lborel (slp_localized_cauchy_kernel 1)"
    by (rule slp_cutoff_annular_weighted_bound[
          OF delta_positive L_nonnegative M_nonnegative])
  have square_near:
    "M * integral\<^sup>L lborel (slp_annular_J1_integrand delta z) \<le>
      (M / delta) *
        integral\<^sup>L lborel (slp_localized_cauchy_kernel 1)"
    by (rule slp_J1_amplitude_weighted_bound[
          OF delta_positive M_nonnegative])
  have identity:
    "(3 * L * M / delta) *
          integral\<^sup>L lborel (slp_localized_cauchy_kernel 1) +
        (M / delta) *
          integral\<^sup>L lborel (slp_localized_cauchy_kernel 1) =
      ((3 * L + 1) * M / delta) *
        integral\<^sup>L lborel (slp_localized_cauchy_kernel 1)"
    by (simp add: algebra_simps add_divide_distrib)
  show ?thesis
    using cutoff square_near identity by linarith
qed

end
