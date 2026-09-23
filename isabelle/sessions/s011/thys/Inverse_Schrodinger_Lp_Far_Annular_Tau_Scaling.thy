theory Inverse_Schrodinger_Lp_Far_Annular_Tau_Scaling
  imports Inverse_Schrodinger_Lp_Far_Annular_Parameter_Choice
begin

section \<open>The integration-by-parts factor on the far envelope\<close>

lemma slp_full_annular_far_tau_scaled_bound:
  assumes tau_positive: "0 < tau"
    and normalized_lower: "1 \<le> R * sqrt tau"
    and L_nonnegative: "0 \<le> L"
    and M_nonnegative: "0 \<le> M"
  shows "(1 / tau) *
      (((L * sqrt tau) * M *
            (integral\<^sup>L lborel
                (slp_annular_I1_integrand (inverse (sqrt tau)) z) +
              integral\<^sup>L lborel
                (slp_annular_I2_integrand (inverse (sqrt tau)) z)) +
          M * integral\<^sup>L lborel
            (slp_annular_J1_full_integrand
              (inverse (sqrt tau)) R z)) +
        M * integral\<^sup>L lborel
          (slp_annular_J2_full_integrand
            (inverse (sqrt tau)) R z)) \<le>
    inverse (sqrt tau) *
      ((((3 * L + 1) * M) *
          integral\<^sup>L lborel (slp_localized_cauchy_kernel 1)) +
        M * (1 + log 2 (R * sqrt tau)) *
          integral\<^sup>L lborel (slp_squared_radial_annulus 1 2))"
proof -
  note envelope =
    slp_full_annular_far_inverse_sqrt_parameter_bound[OF
      tau_positive normalized_lower L_nonnegative M_nonnegative,
      where z = z]
  have scale_nonnegative: "0 \<le> 1 / tau"
    using tau_positive by simp
  have scaled:
    "(1 / tau) *
        (((L * sqrt tau) * M *
              (integral\<^sup>L lborel
                  (slp_annular_I1_integrand (inverse (sqrt tau)) z) +
                integral\<^sup>L lborel
                  (slp_annular_I2_integrand (inverse (sqrt tau)) z)) +
            M * integral\<^sup>L lborel
              (slp_annular_J1_full_integrand
                (inverse (sqrt tau)) R z)) +
          M * integral\<^sup>L lborel
            (slp_annular_J2_full_integrand
              (inverse (sqrt tau)) R z)) \<le>
      (1 / tau) *
        (((((3 * L + 1) * M) * sqrt tau) *
            integral\<^sup>L lborel (slp_localized_cauchy_kernel 1)) +
          (M * sqrt tau) * (1 + log 2 (R * sqrt tau)) *
            integral\<^sup>L lborel (slp_squared_radial_annulus 1 2))"
    by (rule mult_left_mono[OF envelope scale_nonnegative])
  have root_ratio: "sqrt tau / tau = inverse (sqrt tau)"
    by (rule sqrt_divide_self_eq[OF less_imp_le[OF tau_positive]])
  have rhs_normalization:
    "(1 / tau) *
        (((((3 * L + 1) * M) * sqrt tau) *
            integral\<^sup>L lborel (slp_localized_cauchy_kernel 1)) +
          (M * sqrt tau) * (1 + log 2 (R * sqrt tau)) *
            integral\<^sup>L lborel (slp_squared_radial_annulus 1 2)) =
      inverse (sqrt tau) *
        ((((3 * L + 1) * M) *
            integral\<^sup>L lborel (slp_localized_cauchy_kernel 1)) +
          M * (1 + log 2 (R * sqrt tau)) *
            integral\<^sup>L lborel (slp_squared_radial_annulus 1 2))"
  proof -
    have polynomial_normalization:
      "(1 / tau) *
          (((((3 * L + 1) * M) * sqrt tau) *
              integral\<^sup>L lborel (slp_localized_cauchy_kernel 1)) +
            (M * sqrt tau) * (1 + log 2 (R * sqrt tau)) *
              integral\<^sup>L lborel (slp_squared_radial_annulus 1 2)) =
        (sqrt tau / tau) *
          ((((3 * L + 1) * M) *
              integral\<^sup>L lborel (slp_localized_cauchy_kernel 1)) +
            M * (1 + log 2 (R * sqrt tau)) *
              integral\<^sup>L lborel (slp_squared_radial_annulus 1 2))"
      by (simp add: divide_inverse algebra_simps)
    show ?thesis
      using polynomial_normalization root_ratio by simp
  qed
  show ?thesis
    using scaled by (simp only: rhs_normalization)
qed

end
