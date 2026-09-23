theory Inverse_Schrodinger_Lp_Born_Zero_Uniform_Power
  imports Inverse_Schrodinger_Lp_Born_All_Order_Uniform_Power
begin

section \<open>Uniform finite-power control at order zero\<close>

lemma slp_positive_ennreal_lp_product_power_bound:
  assumes a_positive: "0 < a"
    and q_scale: "1 < q / a"
    and r_scale: "1 < r / a"
    and conjugate_scales: "1 / (q / a) + 1 / (r / a) = 1"
    and F_lp: "slp_positive_ennreal_lp_on_plane q F"
    and G_lp: "slp_positive_ennreal_lp_on_plane r G"
  shows "integral\<^sup>L lborel
      (\<lambda>x. enn2real (F x * G x) powr a) \<le>
    integral\<^sup>L lborel (\<lambda>x. enn2real (F x) powr q) / (q / a) +
      integral\<^sup>L lborel (\<lambda>x. enn2real (G x) powr r) / (r / a)"
proof -
  let ?Q = "q / a"
  let ?S = "r / a"
  let ?majorant = "\<lambda>x.
    enn2real (F x) powr q / ?Q + enn2real (G x) powr r / ?S"
  have F_power_integrable:
      "integrable lborel (\<lambda>x. enn2real (F x) powr q)"
    and G_power_integrable:
      "integrable lborel (\<lambda>x. enn2real (G x) powr r)"
    using F_lp G_lp unfolding slp_positive_ennreal_lp_on_plane_def by blast+
  have Q_nonzero: "?Q \<noteq> 0" and S_nonzero: "?S \<noteq> 0"
    using q_scale r_scale by linarith+
  have Q_positive: "0 < ?Q" and S_positive: "0 < ?S"
    using q_scale r_scale by linarith+
  have majorant_integrable: "integrable lborel ?majorant"
    using F_power_integrable G_power_integrable Q_nonzero S_nonzero by simp
  have product_lp:
      "slp_positive_ennreal_lp_on_plane a (\<lambda>x. F x * G x)"
    by (rule slp_positive_ennreal_lp_product[OF a_positive q_scale r_scale
          conjugate_scales F_lp G_lp])
  have product_power_integrable:
      "integrable lborel (\<lambda>x. enn2real (F x * G x) powr a)"
    using product_lp unfolding slp_positive_ennreal_lp_on_plane_def by blast
  have pointwise:
      "enn2real (F x * G x) powr a \<le> ?majorant x" for x
  proof -
    have scale_products: "a * ?Q = q" "a * ?S = r"
      using a_positive by simp_all
    have young:
        "(enn2real (F x) powr a) * (enn2real (G x) powr a) \<le>
          (enn2real (F x) powr a) powr ?Q / ?Q +
          (enn2real (G x) powr a) powr ?S / ?S"
      by (rule Youngs_inequality[OF q_scale r_scale conjugate_scales])
        simp_all
    show ?thesis
      using young a_positive
      by (simp add: enn2real_mult powr_mult powr_powr scale_products)
  qed
  have integral_bound:
      "integral\<^sup>L lborel
          (\<lambda>x. enn2real (F x * G x) powr a) \<le>
        integral\<^sup>L lborel ?majorant"
    by (rule integral_mono[OF product_power_integrable majorant_integrable
          pointwise])
  show ?thesis
    using integral_bound F_power_integrable G_power_integrable
      Q_nonzero S_nonzero
    by simp
qed

lemma slp_positive_ennreal_lp_bounded_multiplier_power_bound:
  assumes exponent_positive: "0 < a"
    and h_measurable: "h \<in> borel_measurable lborel"
    and h_nonnegative: "\<And>x. 0 \<le> h x"
    and h_bound: "\<And>x. h x \<le> C"
    and C_nonnegative: "0 \<le> C"
    and F_lp: "slp_positive_ennreal_lp_on_plane a F"
  shows "integral\<^sup>L lborel
      (\<lambda>x. enn2real (ennreal (h x) * F x) powr a) \<le>
    C powr a * integral\<^sup>L lborel (\<lambda>x. enn2real (F x) powr a)"
proof -
  have F_finite: "AE x in lborel. F x < top"
    and F_power_integrable:
      "integrable lborel (\<lambda>x. enn2real (F x) powr a)"
    using F_lp unfolding slp_positive_ennreal_lp_on_plane_def by blast+
  have scaled_integrable:
      "integrable lborel
        (\<lambda>x. C powr a * enn2real (F x) powr a)"
    using F_power_integrable by simp
  have product_lp:
      "slp_positive_ennreal_lp_on_plane a
        (\<lambda>x. ennreal (h x) * F x)"
    by (rule slp_positive_ennreal_lp_bounded_multiplier[OF exponent_positive
          h_measurable h_nonnegative h_bound C_nonnegative F_lp])
  have product_power_integrable:
      "integrable lborel
        (\<lambda>x. enn2real (ennreal (h x) * F x) powr a)"
    using product_lp unfolding slp_positive_ennreal_lp_on_plane_def by blast
  have exponent_nonnegative: "0 \<le> a"
    using exponent_positive by simp
  have pointwise:
      "AE x in lborel.
        enn2real (ennreal (h x) * F x) powr a \<le>
          C powr a * enn2real (F x) powr a"
    using F_finite
  proof eventually_elim
    fix x :: slp_point
    assume F_x_finite: "F x < top"
    have h_power_le: "h x powr a \<le> C powr a"
      by (rule powr_mono2[OF exponent_nonnegative h_nonnegative h_bound])
    have scaled_power_le:
        "h x powr a * enn2real (F x) powr a \<le>
          C powr a * enn2real (F x) powr a"
      by (rule mult_right_mono[OF h_power_le]) simp
    show "enn2real (ennreal (h x) * F x) powr a \<le>
        C powr a * enn2real (F x) powr a"
      using scaled_power_le F_x_finite h_nonnegative[of x] C_nonnegative
      by (simp add: enn2real_mult powr_mult)
  qed
  have integral_bound:
      "integral\<^sup>L lborel
          (\<lambda>x. enn2real (ennreal (h x) * F x) powr a) \<le>
        integral\<^sup>L lborel
          (\<lambda>x. C powr a * enn2real (F x) powr a)"
    by (rule integral_mono_AE[OF product_power_integrable scaled_integrable
          pointwise])
  show ?thesis
    using integral_bound F_power_integrable by simp
qed

theorem slp_positive_output_density_zero_uniform_power:
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
  shows base_lp:
      "slp_positive_ennreal_lp_on_plane a
        (slp_positive_output_density R cutoff potential terminal_weight 0
          origin)"
    and base_power_bound:
      "integral\<^sup>L lborel
          (\<lambda>output.
            enn2real
              (slp_positive_output_density R cutoff potential terminal_weight 0
                origin output) powr a) \<le>
        (inverse pi * C) powr a *
          (integral\<^sup>L lborel
              (\<lambda>x. abs (slp_localized_cauchy_kernel R x) powr gamma) /
              (gamma / a) +
            integral\<^sup>L lborel
              (\<lambda>x. enn2real (terminal_weight x) powr r) / (r / a))"
proof -
  show base_lp:
      "slp_positive_ennreal_lp_on_plane a
        (slp_positive_output_density R cutoff potential terminal_weight 0
          origin)"
    by (rule slp_positive_output_density_zero_finite_lp[OF exponent_positive
          gamma_lower gamma_upper gamma_scale r_scale conjugate_scales
          terminal_lp cutoff_measurable cutoff_bound C_nonnegative])
  let ?kernel = "\<lambda>output.
    ennreal (slp_localized_cauchy_kernel R (origin - output))"
  let ?h = "\<lambda>output. inverse pi * norm (cutoff output)"
  have kernel_lp: "slp_positive_ennreal_lp_on_plane gamma ?kernel"
    by (rule slp_localized_cauchy_kernel_positive_ennreal_lp[
          OF gamma_lower gamma_upper])
  have product_lp:
      "slp_positive_ennreal_lp_on_plane a
        (\<lambda>output. ?kernel output * terminal_weight output)"
    by (rule slp_positive_ennreal_lp_product[OF exponent_positive gamma_scale
          r_scale conjugate_scales kernel_lp terminal_lp])
  have product_bound:
      "integral\<^sup>L lborel
          (\<lambda>output.
            enn2real (?kernel output * terminal_weight output) powr a) \<le>
        integral\<^sup>L lborel
            (\<lambda>output. enn2real (?kernel output) powr gamma) /
            (gamma / a) +
          integral\<^sup>L lborel
            (\<lambda>output. enn2real (terminal_weight output) powr r) /
            (r / a)"
    by (rule slp_positive_ennreal_lp_product_power_bound[OF exponent_positive
          gamma_scale r_scale conjugate_scales kernel_lp terminal_lp])
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
  have weighted_bound:
      "integral\<^sup>L lborel
          (\<lambda>output.
            enn2real
              (ennreal (?h output) *
                (?kernel output * terminal_weight output)) powr a) \<le>
        (inverse pi * C) powr a *
          integral\<^sup>L lborel
            (\<lambda>output.
              enn2real
                (?kernel output * terminal_weight output) powr a)"
    by (rule slp_positive_ennreal_lp_bounded_multiplier_power_bound[
          OF exponent_positive h_measurable h_nonnegative h_bound
            scaled_C_nonnegative product_lp])
  have kernel_integral:
      "integral\<^sup>L lborel
          (\<lambda>output. enn2real (?kernel output) powr gamma) =
        integral\<^sup>L lborel
          (\<lambda>x. abs (slp_localized_cauchy_kernel R x) powr gamma)"
    using slp_localized_cauchy_kernel_power_translate_integral[
        OF gamma_lower gamma_upper, of R origin]
      slp_localized_cauchy_kernel_nonnegative
    by simp
  have coefficient_nonnegative:
      "0 \<le> (inverse pi * C) powr a"
    by simp
  have scaled_product_bound:
      "(inverse pi * C) powr a *
          integral\<^sup>L lborel
            (\<lambda>output.
              enn2real
                (?kernel output * terminal_weight output) powr a) \<le>
        (inverse pi * C) powr a *
          (integral\<^sup>L lborel
              (\<lambda>x. abs (slp_localized_cauchy_kernel R x) powr gamma) /
              (gamma / a) +
            integral\<^sup>L lborel
              (\<lambda>x. enn2real (terminal_weight x) powr r) / (r / a))"
    by (rule mult_left_mono[OF _ coefficient_nonnegative])
      (use product_bound kernel_integral in simp)
  have density_eq:
      "slp_positive_output_density R cutoff potential terminal_weight 0
          origin =
        (\<lambda>output.
          ennreal (?h output) *
            (?kernel output * terminal_weight output))"
    by (rule ext)
      (simp add: ennreal_mult mult.commute mult.left_commute mult.assoc)
  show base_power_bound:
      "integral\<^sup>L lborel
          (\<lambda>output.
            enn2real
              (slp_positive_output_density R cutoff potential terminal_weight 0
                origin output) powr a) \<le>
        (inverse pi * C) powr a *
          (integral\<^sup>L lborel
              (\<lambda>x. abs (slp_localized_cauchy_kernel R x) powr gamma) /
              (gamma / a) +
            integral\<^sup>L lborel
              (\<lambda>x. enn2real (terminal_weight x) powr r) / (r / a))"
    unfolding density_eq
    using weighted_bound scaled_product_bound by linarith
qed

end
