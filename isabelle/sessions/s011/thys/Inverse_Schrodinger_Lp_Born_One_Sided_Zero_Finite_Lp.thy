theory Inverse_Schrodinger_Lp_Born_One_Sided_Zero_Finite_Lp
  imports Inverse_Schrodinger_Lp_Positive_Ennreal_Lp
begin

section \<open>The order-zero one-sided density at finite exponents\<close>

lemma slp_positive_ennreal_lp_bounded_multiplier:
  assumes exponent_positive: "0 < a"
    and h_measurable: "h \<in> borel_measurable lborel"
    and h_nonnegative: "\<And>x. 0 \<le> h x"
    and h_bound: "\<And>x. h x \<le> C"
    and C_nonnegative: "0 \<le> C"
    and F_lp: "slp_positive_ennreal_lp_on_plane a F"
  shows
    "slp_positive_ennreal_lp_on_plane a
      (\<lambda>x. ennreal (h x) * F x)"
proof -
  have F_measurable: "F \<in> borel_measurable lborel"
    and F_finite: "AE x in lborel. F x < top"
    and F_power_integrable:
      "integrable lborel (\<lambda>x. enn2real (F x) powr a)"
    using F_lp unfolding slp_positive_ennreal_lp_on_plane_def by blast+
  have product_measurable:
      "(\<lambda>x. ennreal (h x) * F x) \<in> borel_measurable lborel"
    using h_measurable F_measurable by measurable
  have product_finite:
      "AE x in lborel. ennreal (h x) * F x < top"
    using F_finite
  proof eventually_elim
    fix x :: slp_point
    assume "F x < top"
    then show "ennreal (h x) * F x < top"
      by (simp add: ennreal_mult_less_top)
  qed
  have majorant_integrable:
      "integrable lborel
        (\<lambda>x. (C powr a) * (enn2real (F x) powr a))"
    using F_power_integrable by simp
  have product_power_measurable:
      "(\<lambda>x. enn2real (ennreal (h x) * F x) powr a)
        \<in> borel_measurable lborel"
    using product_measurable by measurable
  have product_power_integrable:
      "integrable lborel
        (\<lambda>x. enn2real (ennreal (h x) * F x) powr a)"
  proof (rule Bochner_Integration.integrable_bound[OF majorant_integrable
        product_power_measurable])
    show "AE x in lborel.
        norm (enn2real (ennreal (h x) * F x) powr a) \<le>
          norm ((C powr a) * (enn2real (F x) powr a))"
    using F_finite
    proof eventually_elim
      fix x :: slp_point
      assume F_x_finite: "F x < top"
      have exponent_nonnegative: "0 \<le> a"
        using exponent_positive by simp
      have h_power_le: "h x powr a \<le> C powr a"
        by (rule powr_mono2[OF exponent_nonnegative h_nonnegative h_bound])
      have scaled_power_le:
          "(h x powr a) * (enn2real (F x) powr a) \<le>
            (C powr a) * (enn2real (F x) powr a)"
        by (rule mult_right_mono[OF h_power_le]) simp
      show "norm (enn2real (ennreal (h x) * F x) powr a) \<le>
          norm ((C powr a) * (enn2real (F x) powr a))"
        using scaled_power_le F_x_finite h_nonnegative[of x] C_nonnegative
        by (simp add: enn2real_mult powr_mult)
    qed
  qed
  show ?thesis
    unfolding slp_positive_ennreal_lp_on_plane_def
    using product_measurable product_finite product_power_integrable by blast
qed

lemma slp_localized_cauchy_kernel_positive_ennreal_lp:
  assumes exponent_lower: "1 \<le> gamma"
    and exponent_upper: "gamma < 2"
  shows
    "slp_positive_ennreal_lp_on_plane gamma
      (\<lambda>output.
        ennreal (slp_localized_cauchy_kernel R (origin - output)))"
proof -
  have kernel_measurable:
      "(\<lambda>output.
        ennreal (slp_localized_cauchy_kernel R (origin - output)))
        \<in> borel_measurable lborel"
    using slp_localized_cauchy_kernel_borel_measurable by measurable
  have kernel_finite:
      "AE output in lborel.
        ennreal (slp_localized_cauchy_kernel R (origin - output)) < top"
    by simp
  have kernel_power_integrable:
      "integrable lborel
        (\<lambda>output.
          enn2real
            (ennreal (slp_localized_cauchy_kernel R (origin - output)))
            powr gamma)"
    using slp_localized_cauchy_kernel_power_translate_integrable[
        OF exponent_lower exponent_upper, of R origin]
    by (simp add: slp_localized_cauchy_kernel_nonnegative)
  show ?thesis
    unfolding slp_positive_ennreal_lp_on_plane_def
    using kernel_measurable kernel_finite kernel_power_integrable by blast
qed

theorem slp_positive_output_density_zero_finite_lp:
  assumes exponent_positive: "0 < a"
    and gamma_lower: "1 \<le> gamma"
    and gamma_upper: "gamma < 2"
    and gamma_scale: "1 < gamma / a"
    and r_scale: "1 < r / a"
    and conjugate_scales: "1 / (gamma / a) + 1 / (r / a) = 1"
    and terminal_lp: "slp_positive_ennreal_lp_on_plane r terminal_weight"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
  shows
    "slp_positive_ennreal_lp_on_plane a
      (slp_positive_output_density R cutoff potential terminal_weight 0 origin)"
proof -
  let ?kernel = "\<lambda>output.
    ennreal (slp_localized_cauchy_kernel R (origin - output))"
  have kernel_lp: "slp_positive_ennreal_lp_on_plane gamma ?kernel"
    by (rule slp_localized_cauchy_kernel_positive_ennreal_lp[
          OF gamma_lower gamma_upper])
  have kernel_terminal_lp:
      "slp_positive_ennreal_lp_on_plane a
        (\<lambda>output. ?kernel output * terminal_weight output)"
    by (rule slp_positive_ennreal_lp_product[OF exponent_positive gamma_scale
          r_scale conjugate_scales kernel_lp terminal_lp])
  let ?h = "\<lambda>output. inverse pi * norm (cutoff output)"
  have h_measurable: "?h \<in> borel_measurable lborel"
    using cutoff_measurable by measurable
  have inverse_pi_nonnegative: "0 \<le> inverse pi"
    by simp
  have h_nonnegative: "0 \<le> ?h z" for z
    using inverse_pi_nonnegative by simp
  have h_bound: "?h z \<le> inverse pi * C" for z
    by (rule mult_left_mono[OF cutoff_bound inverse_pi_nonnegative])
  have scaled_C_nonnegative: "0 \<le> inverse pi * C"
    using inverse_pi_nonnegative C_nonnegative by simp
  have weighted_lp:
      "slp_positive_ennreal_lp_on_plane a
        (\<lambda>output.
          ennreal (?h output) *
            (?kernel output * terminal_weight output))"
    by (rule slp_positive_ennreal_lp_bounded_multiplier[OF exponent_positive
          h_measurable h_nonnegative h_bound scaled_C_nonnegative
          kernel_terminal_lp])
  have density_eq:
      "slp_positive_output_density R cutoff potential terminal_weight 0
          origin =
        (\<lambda>output.
          ennreal (?h output) *
            (?kernel output * terminal_weight output))"
    by (rule ext)
      (simp add: ennreal_mult mult.commute mult.left_commute mult.assoc)
  show ?thesis
    unfolding density_eq
    by (rule weighted_lp)
qed

end
