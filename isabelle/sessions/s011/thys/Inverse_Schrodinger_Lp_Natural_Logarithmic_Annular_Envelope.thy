theory Inverse_Schrodinger_Lp_Natural_Logarithmic_Annular_Envelope
  imports Inverse_Schrodinger_Lp_Natural_Logarithmic_Parameter_Comparison
begin

section \<open>The complete natural-logarithmic scalar envelope\<close>

lemma slp_near_far_annular_natural_logarithmic_bound:
  assumes R_lower: "1 \<le> R"
    and tau_lower: "2 \<le> tau"
    and L_nonnegative: "0 \<le> L"
    and f_measurable: "f \<in> borel_measurable lborel"
    and M_nonnegative: "0 \<le> M"
    and f_bound: "\<And>y. norm (f y) \<le> M"
  shows "slp_localized_riesz_potential
        (2 * inverse (sqrt tau)) f z +
      (1 / tau) *
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
    inverse (sqrt tau) * ln (2 + tau) *
      ((((2 * M + (3 * L + 1) * M) *
          integral\<^sup>L lborel (slp_localized_cauchy_kernel 1)) /
            ln 2) +
        M * ((2 + log 2 R) / ln 2) *
          integral\<^sup>L lborel (slp_squared_radial_annulus 1 2))"
proof -
  have tau_positive: "0 < tau"
    using tau_lower by linarith
  have tau_nonnegative: "0 \<le> tau"
    using tau_lower by linarith
  have tau_at_least_one: "1 \<le> tau"
    using tau_lower by linarith
  have sqrt_lower: "1 \<le> sqrt tau"
    using tau_at_least_one by simp
  have R_nonnegative: "0 \<le> R"
    using R_lower by linarith
  have normalized_lower: "1 \<le> R * sqrt tau"
  proof -
    have R_growth: "R \<le> R * sqrt tau"
    proof -
      have "R * 1 \<le> R * sqrt tau"
        by (rule mult_left_mono[OF sqrt_lower R_nonnegative])
      then show ?thesis by simp
    qed
    show ?thesis
      by (rule order_trans[OF R_lower R_growth])
  qed
  note envelope = slp_near_far_annular_inverse_sqrt_bound[OF
      tau_positive normalized_lower L_nonnegative f_measurable
      M_nonnegative f_bound, where z = z]
  note logarithmic = slp_log_sqrt_parameter_natural_bound[OF
      R_lower tau_lower]
  have kernel_mass_nonnegative:
      "0 \<le> integral\<^sup>L lborel (slp_localized_cauchy_kernel 1)"
    by (rule Bochner_Integration.integral_nonneg)
       (simp add: slp_localized_cauchy_kernel_nonnegative)
  have annulus_mass_nonnegative:
      "0 \<le> integral\<^sup>L lborel
        (slp_squared_radial_annulus 1 2)"
    by (rule Bochner_Integration.integral_nonneg) simp
  have L_coefficient_nonnegative: "0 \<le> 3 * L + 1"
    using L_nonnegative by linarith
  have static_coefficient_nonnegative:
      "0 \<le> 2 * M + (3 * L + 1) * M"
  proof -
    have first: "0 \<le> 2 * M"
      by (rule mult_nonneg_nonneg) (simp_all add: M_nonnegative)
    have second: "0 \<le> (3 * L + 1) * M"
      by (rule mult_nonneg_nonneg[OF L_coefficient_nonnegative
            M_nonnegative])
    show ?thesis
      by (rule add_nonneg_nonneg[OF first second])
  qed
  have static_term_nonnegative:
      "0 \<le> (2 * M + (3 * L + 1) * M) *
        integral\<^sup>L lborel (slp_localized_cauchy_kernel 1)"
    by (rule mult_nonneg_nonneg[OF static_coefficient_nonnegative
          kernel_mass_nonnegative])
  have log_growth_at_least_one: "1 \<le> log 2 (2 + tau)"
  proof -
    have "log 2 2 \<le> log 2 (2 + tau)"
    proof (rule log_mono)
      show "(1::real) < 2" by simp
      show "(0::real) < 2" by simp
      show "(2::real) \<le> 2 + tau"
        using tau_lower by linarith
    qed
    then show ?thesis by simp
  qed
  have natural_ratio_at_least_one:
      "1 \<le> ln (2 + tau) / ln 2"
    using log_growth_at_least_one by (simp add: log_def)
  have static_growth:
      "(2 * M + (3 * L + 1) * M) *
          integral\<^sup>L lborel (slp_localized_cauchy_kernel 1) \<le>
        (((2 * M + (3 * L + 1) * M) *
            integral\<^sup>L lborel (slp_localized_cauchy_kernel 1)) /
              ln 2) * ln (2 + tau)"
  proof -
    have weighted:
        "((2 * M + (3 * L + 1) * M) *
            integral\<^sup>L lborel (slp_localized_cauchy_kernel 1)) * 1 \<le>
          ((2 * M + (3 * L + 1) * M) *
            integral\<^sup>L lborel (slp_localized_cauchy_kernel 1)) *
              (ln (2 + tau) / ln 2)"
      by (rule mult_left_mono[OF natural_ratio_at_least_one
            static_term_nonnegative])
    show ?thesis
      using weighted by (simp add: divide_inverse algebra_simps)
  qed
  have logarithmic_weight:
      "M * (1 + log 2 (R * sqrt tau)) *
          integral\<^sup>L lborel (slp_squared_radial_annulus 1 2) \<le>
        M * (((2 + log 2 R) / ln 2) * ln (2 + tau)) *
          integral\<^sup>L lborel (slp_squared_radial_annulus 1 2)"
  proof -
    have first:
        "M * (1 + log 2 (R * sqrt tau)) \<le>
          M * (((2 + log 2 R) / ln 2) * ln (2 + tau))"
      by (rule mult_left_mono[OF logarithmic M_nonnegative])
    show ?thesis
      by (rule mult_right_mono[OF first annulus_mass_nonnegative])
  qed
  have bracket_bound:
      "((2 * M + (3 * L + 1) * M) *
          integral\<^sup>L lborel (slp_localized_cauchy_kernel 1)) +
        M * (1 + log 2 (R * sqrt tau)) *
          integral\<^sup>L lborel (slp_squared_radial_annulus 1 2) \<le>
      ln (2 + tau) *
        ((((2 * M + (3 * L + 1) * M) *
            integral\<^sup>L lborel (slp_localized_cauchy_kernel 1)) /
              ln 2) +
          M * ((2 + log 2 R) / ln 2) *
            integral\<^sup>L lborel (slp_squared_radial_annulus 1 2))"
  proof -
    note combined = add_mono[OF static_growth logarithmic_weight]
    show ?thesis
      using combined by (simp add: algebra_simps)
  qed
  have outer_bound:
      "inverse (sqrt tau) *
          (((2 * M + (3 * L + 1) * M) *
              integral\<^sup>L lborel (slp_localized_cauchy_kernel 1)) +
            M * (1 + log 2 (R * sqrt tau)) *
              integral\<^sup>L lborel (slp_squared_radial_annulus 1 2)) \<le>
        inverse (sqrt tau) * ln (2 + tau) *
          ((((2 * M + (3 * L + 1) * M) *
              integral\<^sup>L lborel (slp_localized_cauchy_kernel 1)) /
                ln 2) +
            M * ((2 + log 2 R) / ln 2) *
              integral\<^sup>L lborel (slp_squared_radial_annulus 1 2))"
  proof -
    have scaled:
        "inverse (sqrt tau) *
            (((2 * M + (3 * L + 1) * M) *
                integral\<^sup>L lborel (slp_localized_cauchy_kernel 1)) +
              M * (1 + log 2 (R * sqrt tau)) *
                integral\<^sup>L lborel
                  (slp_squared_radial_annulus 1 2)) \<le>
          inverse (sqrt tau) *
            (ln (2 + tau) *
              ((((2 * M + (3 * L + 1) * M) *
                  integral\<^sup>L lborel (slp_localized_cauchy_kernel 1)) /
                    ln 2) +
                M * ((2 + log 2 R) / ln 2) *
                  integral\<^sup>L lborel
                    (slp_squared_radial_annulus 1 2)))"
      by (rule mult_left_mono[OF bracket_bound])
         (simp add: tau_nonnegative)
    show ?thesis
      using scaled by (simp add: algebra_simps)
  qed
  show ?thesis
    using envelope outer_bound by linarith
qed

end
