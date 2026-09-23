theory Inverse_Schrodinger_Lp_Near_Center_Operator_Bridge
  imports
    Inverse_Schrodinger_Lp_Natural_Logarithmic_Annular_Envelope
    "HOL-Analysis.Ball_Volume"
begin

section \<open>The uniform near-center operator bound\<close>

definition slp_near_center_scalar_kernel ::
  "real \<Rightarrow> slp_point \<Rightarrow> slp_point \<Rightarrow>
    slp_point \<Rightarrow> real"
where
  "slp_near_center_scalar_kernel delta c z y =
    (if norm (y - c) \<le> 2 * delta then
      slp_radial_inverse (z - y)
    else 0)"

lemma slp_near_center_scalar_kernel_measurable [measurable]:
  "slp_near_center_scalar_kernel delta c z \<in> borel_measurable lborel"
  unfolding slp_near_center_scalar_kernel_def by measurable

lemma slp_near_center_scalar_kernel_nonnegative [simp]:
  "0 \<le> slp_near_center_scalar_kernel delta c z y"
  unfolding slp_near_center_scalar_kernel_def by simp

lemma slp_cauchy_kernel_norm [simp]:
  "norm (slp_cauchy_kernel orientation z y) =
    slp_radial_inverse (z - y)"
proof -
  have difference:
    "slp_point_as_complex z - slp_point_as_complex y =
      slp_point_as_complex (z - y)"
    by (rule sym) (rule slp_point_as_complex_diff)
  have denominator_norm:
    "norm (slp_cauchy_denominator orientation z y) = norm (z - y)"
  proof (cases orientation)
    case SLP_Partial_Inverse
    show ?thesis
      using SLP_Partial_Inverse
      by (simp only: slp_cauchy_denominator_def
          slp_cauchy_orientation.simps difference complex_mod_cnj
          slp_point_as_complex_norm)
  next
    case SLP_Dbar_Inverse
    show ?thesis
      using SLP_Dbar_Inverse
      by (simp only: slp_cauchy_denominator_def
          slp_cauchy_orientation.simps difference
          slp_point_as_complex_norm)
  qed
  show ?thesis
    unfolding slp_cauchy_kernel_def slp_radial_inverse_def
    by (simp only: norm_inverse denominator_norm)
qed

lemma slp_near_center_scalar_integrable:
  assumes delta_positive: "0 < delta"
  shows "integrable lborel (slp_near_center_scalar_kernel delta c z)"
proof (cases "norm (z - c) \<le> 4 * delta")
  case True
  let ?majorant = "\<lambda>y.
    slp_localized_cauchy_kernel (6 * delta) (z - y)"
  have majorant_integrable: "integrable lborel ?majorant"
    by (rule slp_localized_cauchy_kernel_translate_integrable)
  show ?thesis
  proof (rule Bochner_Integration.integrable_bound[OF majorant_integrable])
    show "slp_near_center_scalar_kernel delta c z \<in>
        borel_measurable lborel"
      by measurable
    show "AE y in lborel.
        norm (slp_near_center_scalar_kernel delta c z y) \<le>
          norm (?majorant y)"
    proof (rule AE_I2)
      fix y :: slp_point
      show "norm (slp_near_center_scalar_kernel delta c z y) \<le>
          norm (?majorant y)"
      proof (cases "norm (y - c) \<le> 2 * delta")
        case inside: True
        have distance: "norm (z - y) \<le> 6 * delta"
        proof -
          have "norm (z - y) \<le> norm (z - c) + norm (y - c)"
            using norm_triangle_ineq[of "z - c" "c - y"]
            by (simp add: norm_minus_commute)
          also have "... \<le> 6 * delta"
            using True inside by linarith
          finally show ?thesis .
        qed
        show ?thesis
          using inside distance
          by (simp add: slp_near_center_scalar_kernel_def
              slp_localized_cauchy_kernel_def slp_radial_inverse_def)
      next
        case False
        show ?thesis
          using delta_positive
          by (simp add: slp_near_center_scalar_kernel_def False
              slp_localized_cauchy_kernel_nonnegative)
      qed
    qed
  qed
next
  case False
  let ?ball = "cball c (2 * delta)"
  let ?majorant = "\<lambda>y. inverse (2 * delta) * indicator ?ball y"
  have ball_measurable: "?ball \<in> sets (lborel :: slp_point measure)"
    by measurable
  have ball_finite: "emeasure lborel ?ball < \<infinity>"
    by (rule emeasure_lborel_cball_finite)
  have majorant_integrable: "integrable lborel ?majorant"
    using ball_measurable ball_finite by simp
  show ?thesis
  proof (rule Bochner_Integration.integrable_bound[OF majorant_integrable])
    show "slp_near_center_scalar_kernel delta c z \<in>
        borel_measurable lborel"
      by measurable
    show "AE y in lborel.
        norm (slp_near_center_scalar_kernel delta c z y) \<le>
          norm (?majorant y)"
    proof (rule AE_I2)
      fix y :: slp_point
      show "norm (slp_near_center_scalar_kernel delta c z y) \<le>
          norm (?majorant y)"
      proof (cases "norm (y - c) \<le> 2 * delta")
        case inside: True
        have separation: "2 * delta \<le> norm (z - y)"
        proof -
          have reverse: "norm (z - c) \<le> norm (z - y) + norm (y - c)"
            using norm_triangle_ineq[of "z - y" "y - c"] by simp
          show ?thesis
            using reverse inside False by linarith
        qed
        have radial_bound:
          "slp_radial_inverse (z - y) \<le> inverse (2 * delta)"
        proof -
          have two_delta_positive: "0 < 2 * delta"
            using delta_positive by linarith
          have bound:
            "slp_radial_inverse (z - y) \<le> 1 / (2 * delta)"
            by (rule slp_radial_inverse_bound[where
                  delta = "2 * delta" and x = "z - y", OF
                  two_delta_positive separation])
          show ?thesis
            using bound by (simp only: divide_inverse)
        qed
        show ?thesis
          using inside radial_bound delta_positive
          by (simp add: slp_near_center_scalar_kernel_def
              indicator_def dist_norm norm_minus_commute)
      next
        case outside: False
        show ?thesis
          using outside delta_positive
          by (simp add: slp_near_center_scalar_kernel_def
              indicator_def dist_norm)
      qed
    qed
  qed
qed

lemma slp_near_center_scalar_integral_bound:
  assumes delta_positive: "0 < delta"
  shows "integral\<^sup>L lborel
      (slp_near_center_scalar_kernel delta c z) \<le>
    delta * (6 * integral\<^sup>L lborel
      (slp_localized_cauchy_kernel 1) + 2 * unit_ball_vol 2)"
proof (cases "norm (z - c) \<le> 4 * delta")
  case True
  let ?majorant = "\<lambda>y.
    slp_localized_cauchy_kernel (6 * delta) (z - y)"
  have integrand_integrable:
    "integrable lborel (slp_near_center_scalar_kernel delta c z)"
    by (rule slp_near_center_scalar_integrable[OF delta_positive])
  have majorant_integrable: "integrable lborel ?majorant"
    by (rule slp_localized_cauchy_kernel_translate_integrable)
  have pointwise: "\<And>y. slp_near_center_scalar_kernel delta c z y \<le>
      ?majorant y"
  proof -
    fix y :: slp_point
    show "slp_near_center_scalar_kernel delta c z y \<le> ?majorant y"
    proof (cases "norm (y - c) \<le> 2 * delta")
      case inside: True
      have distance: "norm (z - y) \<le> 6 * delta"
      proof -
        have "norm (z - y) \<le> norm (z - c) + norm (y - c)"
          using norm_triangle_ineq[of "z - c" "c - y"]
          by (simp add: norm_minus_commute)
        also have "... \<le> 6 * delta"
          using True inside by linarith
        finally show ?thesis .
      qed
      show ?thesis
        using inside distance
        by (simp add: slp_near_center_scalar_kernel_def
            slp_localized_cauchy_kernel_def slp_radial_inverse_def)
    next
      case False
      show ?thesis
        by (simp add: slp_near_center_scalar_kernel_def False
            slp_localized_cauchy_kernel_nonnegative)
    qed
  qed
  have integral_le:
    "integral\<^sup>L lborel (slp_near_center_scalar_kernel delta c z) \<le>
      integral\<^sup>L lborel ?majorant"
    by (rule Bochner_Integration.integral_mono[OF integrand_integrable
          majorant_integrable]) (rule pointwise)
  have translated:
    "integral\<^sup>L lborel ?majorant =
      integral\<^sup>L lborel (slp_localized_cauchy_kernel (6 * delta))"
    by (rule slp_localized_cauchy_kernel_reflected_translate_integral)
  have scaling:
    "integral\<^sup>L lborel (slp_localized_cauchy_kernel (6 * delta)) =
      (6 * delta) * integral\<^sup>L lborel
        (slp_localized_cauchy_kernel 1)"
    by (rule slp_localized_cauchy_kernel_integral_scale)
      (use delta_positive in simp)
  have ball_term_nonnegative: "0 \<le> 2 * delta * unit_ball_vol 2"
    using delta_positive by simp
  show ?thesis
    using integral_le translated scaling ball_term_nonnegative
    by (simp add: algebra_simps)
next
  case False
  let ?ball = "cball c (2 * delta)"
  let ?majorant = "\<lambda>y. inverse (2 * delta) * indicator ?ball y"
  have ball_measurable: "?ball \<in> sets (lborel :: slp_point measure)"
    by measurable
  have ball_finite: "emeasure lborel ?ball < \<infinity>"
    by (rule emeasure_lborel_cball_finite)
  have integrand_integrable:
    "integrable lborel (slp_near_center_scalar_kernel delta c z)"
    by (rule slp_near_center_scalar_integrable[OF delta_positive])
  have majorant_integrable: "integrable lborel ?majorant"
    using ball_measurable ball_finite by simp
  have pointwise: "\<And>y. slp_near_center_scalar_kernel delta c z y \<le>
      ?majorant y"
  proof -
    fix y :: slp_point
    show "slp_near_center_scalar_kernel delta c z y \<le> ?majorant y"
    proof (cases "norm (y - c) \<le> 2 * delta")
      case inside: True
      have separation: "2 * delta \<le> norm (z - y)"
      proof -
        have reverse: "norm (z - c) \<le> norm (z - y) + norm (y - c)"
          using norm_triangle_ineq[of "z - y" "y - c"] by simp
        show ?thesis
          using reverse inside False by linarith
      qed
      have radial_bound:
        "slp_radial_inverse (z - y) \<le> inverse (2 * delta)"
      proof -
        have two_delta_positive: "0 < 2 * delta"
          using delta_positive by linarith
        have bound:
          "slp_radial_inverse (z - y) \<le> 1 / (2 * delta)"
          by (rule slp_radial_inverse_bound[where
                delta = "2 * delta" and x = "z - y", OF
                two_delta_positive separation])
        show ?thesis
          using bound by (simp only: divide_inverse)
      qed
      show ?thesis
        using inside radial_bound
        by (simp add: slp_near_center_scalar_kernel_def
            indicator_def dist_norm norm_minus_commute)
next
  case outside: False
  show ?thesis
    using outside delta_positive
    by (simp add: slp_near_center_scalar_kernel_def
        indicator_def dist_norm norm_minus_commute)
qed
  qed
  have integral_le:
    "integral\<^sup>L lborel (slp_near_center_scalar_kernel delta c z) \<le>
      integral\<^sup>L lborel ?majorant"
    by (rule Bochner_Integration.integral_mono[OF integrand_integrable
          majorant_integrable]) (rule pointwise)
  have ball_measure:
    "measure lborel ?ball = unit_ball_vol 2 * (2 * delta) ^ 2"
    using content_cball[where c = c and r = "2 * delta"] delta_positive
    by (simp add: content_def)
  have majorant_integral:
    "integral\<^sup>L lborel ?majorant =
      inverse (2 * delta) * measure lborel ?ball"
    using ball_measurable ball_finite
    by simp
  have normalized:
    "inverse (2 * delta) * (unit_ball_vol 2 * (2 * delta) ^ 2) =
      2 * delta * unit_ball_vol 2"
  proof -
    have delta_nonzero: "delta \<noteq> 0"
      using delta_positive by linarith
    show ?thesis
      using delta_nonzero
      by (simp add: power2_eq_square algebra_simps)
  qed
  have kernel_term_nonnegative:
    "0 \<le> 6 * delta * integral\<^sup>L lborel
      (slp_localized_cauchy_kernel 1)"
  proof -
    have coefficient_nonnegative: "0 \<le> 6 * delta"
      using delta_positive by linarith
    have kernel_mass_nonnegative:
        "0 \<le> integral\<^sup>L lborel (slp_localized_cauchy_kernel 1)"
      by (rule Bochner_Integration.integral_nonneg)
         (simp add: slp_localized_cauchy_kernel_nonnegative)
    show ?thesis
      by (rule mult_nonneg_nonneg[OF coefficient_nonnegative
            kernel_mass_nonnegative])
  qed
  have ball_bound:
      "integral\<^sup>L lborel
          (slp_near_center_scalar_kernel delta c z) \<le>
        2 * delta * unit_ball_vol 2"
  proof -
    from integral_le have
        "integral\<^sup>L lborel
            (slp_near_center_scalar_kernel delta c z) \<le>
          integral\<^sup>L lborel ?majorant" .
    also have "integral\<^sup>L lborel ?majorant =
        inverse (2 * delta) * measure lborel ?ball"
      by (rule majorant_integral)
    also have "... = inverse (2 * delta) *
        (unit_ball_vol 2 * (2 * delta) ^ 2)"
      using ball_measure by simp
    also have "... = 2 * delta * unit_ball_vol 2"
      by (rule normalized)
    finally show ?thesis .
  qed
  have target_identity:
      "delta *
          (6 * integral\<^sup>L lborel
              (slp_localized_cauchy_kernel 1) +
           2 * unit_ball_vol 2) =
        2 * delta * unit_ball_vol 2 +
        6 * delta * integral\<^sup>L lborel
          (slp_localized_cauchy_kernel 1)"
    by (simp add: algebra_simps)
  show ?thesis
    using ball_bound kernel_term_nonnegative target_identity
    by linarith
qed

context slp_cutoff_profile
begin

definition slp_near_cutoff_amplitude ::
  "real \<Rightarrow> slp_point \<Rightarrow> slp_scalar_field \<Rightarrow>
    slp_scalar_field"
where
  "slp_near_cutoff_amplitude delta c f y =
    of_real (slp_scaled_cutoff delta c y) * f y"

lemma slp_scaled_cutoff_borel_measurable [measurable]:
  "slp_scaled_cutoff delta c \<in> borel_measurable lborel"
proof -
  have continuous_cutoff:
    "continuous_on UNIV (slp_scaled_cutoff delta c)"
  proof (rule continuous_at_imp_continuous_on)
    show "\<forall>z \<in> UNIV. isCont (slp_scaled_cutoff delta c) z"
      by (intro ballI has_derivative_continuous[OF
            slp_scaled_cutoff_has_derivative])
  qed
  have borel: "slp_scaled_cutoff delta c \<in> borel_measurable borel"
    by (rule borel_measurable_continuous_onI[OF continuous_cutoff])
  show ?thesis
  proof (rule borel_measurable_subalgebra[where N=borel])
    show "sets borel \<subseteq> sets (lborel :: slp_point measure)"
      by simp
    show "space borel = space (lborel :: slp_point measure)"
      by simp
    show "slp_scaled_cutoff delta c \<in> borel_measurable borel"
      by (rule borel)
  qed
qed

lemma slp_near_cutoff_amplitude_measurable:
  assumes f_measurable: "f \<in> borel_measurable lborel"
  shows "slp_near_cutoff_amplitude delta c f \<in>
    borel_measurable lborel"
  unfolding slp_near_cutoff_amplitude_def
  using f_measurable by measurable

lemma slp_near_oscillatory_integrand_norm_bound:
  assumes delta_positive: "0 < delta"
    and M_nonnegative: "0 \<le> M"
    and f_bound: "\<And>y. norm (f y) \<le> M"
  shows "norm (slp_cauchy_integrand orientation
      (slp_oscillatory_modulation tau c
        (slp_near_cutoff_amplitude delta c f)) z y) \<le>
    M * slp_near_center_scalar_kernel delta c z y"
proof (cases "norm (y - c) \<le> 2 * delta")
  case inside: True
  have cutoff_bound: "norm (slp_scaled_cutoff delta c y) \<le> 1"
    by (rule slp_scaled_cutoff_norm)
  have amplitude_bound:
    "norm (slp_near_cutoff_amplitude delta c f y) \<le> M"
  proof -
    have product_bound:
      "norm (slp_scaled_cutoff delta c y) * norm (f y) \<le> 1 * M"
      by (rule mult_mono[OF cutoff_bound f_bound[of y]]) simp_all
    show ?thesis
      using product_bound
      by (simp add: slp_near_cutoff_amplitude_def norm_mult)
  qed
  show ?thesis
    using inside amplitude_bound slp_radial_inverse_nonnegative[of "z - y"]
    by (simp add: slp_cauchy_integrand_def
        slp_near_center_scalar_kernel_def norm_mult
        mult_right_mono)
next
  case outside: False
  have cutoff_zero: "slp_scaled_cutoff delta c y = 0"
    by (rule slp_scaled_cutoff_outer[OF delta_positive])
      (use outside in linarith)
  show ?thesis
    using outside M_nonnegative
    by (simp add: slp_cauchy_integrand_def
        slp_oscillatory_modulation_def
        slp_near_cutoff_amplitude_def
        slp_near_center_scalar_kernel_def cutoff_zero)
qed

lemma slp_near_partial_psi_inverse_uniform_bound:
  assumes delta_positive: "0 < delta"
    and f_measurable: "f \<in> borel_measurable lborel"
    and M_nonnegative: "0 \<le> M"
    and f_bound: "\<And>y. norm (f y) \<le> M"
  shows "norm (slp_partial_psi_inverse tau c
      (slp_near_cutoff_amplitude delta c f) z) \<le>
    norm (inverse (of_real pi :: complex)) * M * delta *
      (6 * integral\<^sup>L lborel (slp_localized_cauchy_kernel 1) +
        2 * unit_ball_vol 2)"
proof -
  let ?g = "slp_oscillatory_modulation tau c
    (slp_near_cutoff_amplitude delta c f)"
  let ?majorant = "\<lambda>y.
    M * slp_near_center_scalar_kernel delta c z y"
  have near_integrable:
    "integrable lborel (slp_near_center_scalar_kernel delta c z)"
    by (rule slp_near_center_scalar_integrable[OF delta_positive])
  have majorant_integrable: "integrable lborel ?majorant"
    using near_integrable by (rule integrable_mult_right)
  have g_measurable: "?g \<in> borel_measurable lborel"
    by (rule slp_oscillatory_modulation_measurable)
      (rule slp_near_cutoff_amplitude_measurable[OF f_measurable])
  have integrand_integrable:
    "integrable lborel (slp_cauchy_integrand SLP_Partial_Inverse ?g z)"
  proof (rule Bochner_Integration.integrable_bound[OF majorant_integrable])
    show "slp_cauchy_integrand SLP_Partial_Inverse ?g z \<in>
        borel_measurable lborel"
      by (rule slp_cauchy_integrand_borel_measurable[OF g_measurable])
    show "AE y in lborel.
        norm (slp_cauchy_integrand SLP_Partial_Inverse ?g z y) \<le>
          norm (?majorant y)"
    proof (rule AE_I2)
      fix y :: slp_point
      have bound:
        "norm (slp_cauchy_integrand SLP_Partial_Inverse ?g z y) \<le>
          ?majorant y"
        by (rule slp_near_oscillatory_integrand_norm_bound[OF
              delta_positive M_nonnegative f_bound])
      have majorant_nonnegative: "0 \<le> ?majorant y"
        using M_nonnegative by simp
      show "norm (slp_cauchy_integrand SLP_Partial_Inverse ?g z y) \<le>
          norm (?majorant y)"
        using bound majorant_nonnegative by simp
    qed
  qed
  have norm_integral_le:
    "integral\<^sup>L lborel
        (\<lambda>y. norm (slp_cauchy_integrand SLP_Partial_Inverse ?g z y))
      \<le> integral\<^sup>L lborel ?majorant"
  proof (rule Bochner_Integration.integral_mono)
    show "integrable lborel
        (\<lambda>y. norm (slp_cauchy_integrand SLP_Partial_Inverse ?g z y))"
      using integrand_integrable by (rule integrable_norm)
    show "integrable lborel ?majorant"
      by (rule majorant_integrable)
    fix y :: slp_point
    assume "y \<in> space lborel"
    show "norm (slp_cauchy_integrand SLP_Partial_Inverse ?g z y) \<le>
        ?majorant y"
      by (rule slp_near_oscillatory_integrand_norm_bound[OF
            delta_positive M_nonnegative f_bound])
  qed
  have majorant_integral:
    "integral\<^sup>L lborel ?majorant =
      M * integral\<^sup>L lborel
        (slp_near_center_scalar_kernel delta c z)"
    using near_integrable by simp
  have scalar_bound:
    "integral\<^sup>L lborel (slp_near_center_scalar_kernel delta c z) \<le>
      delta * (6 * integral\<^sup>L lborel
        (slp_localized_cauchy_kernel 1) + 2 * unit_ball_vol 2)"
    by (rule slp_near_center_scalar_integral_bound[OF delta_positive])
  have scaled_scalar_bound:
    "M * integral\<^sup>L lborel (slp_near_center_scalar_kernel delta c z)
      \<le> M * (delta * (6 * integral\<^sup>L lborel
        (slp_localized_cauchy_kernel 1) + 2 * unit_ball_vol 2))"
    by (rule mult_left_mono[OF scalar_bound M_nonnegative])
  have transform_bound:
    "norm (slp_cauchy_transform SLP_Partial_Inverse ?g z) \<le>
      norm (inverse (of_real pi :: complex)) *
        integral\<^sup>L lborel
          (\<lambda>y. norm
            (slp_cauchy_integrand SLP_Partial_Inverse ?g z y))"
    by (rule slp_cauchy_transform_norm_bound)
  have coefficient_nonnegative:
    "0 \<le> norm (inverse (of_real pi :: complex))"
    by simp
  have transform_to_majorant:
    "norm (slp_cauchy_transform SLP_Partial_Inverse ?g z) \<le>
      norm (inverse (of_real pi :: complex)) *
        integral\<^sup>L lborel ?majorant"
    by (rule order_trans[OF transform_bound
          mult_left_mono[OF norm_integral_le coefficient_nonnegative]])
  have majorant_upper:
    "integral\<^sup>L lborel ?majorant \<le>
      M * (delta * (6 * integral\<^sup>L lborel
        (slp_localized_cauchy_kernel 1) + 2 * unit_ball_vol 2))"
    using majorant_integral scaled_scalar_bound by simp
  have composed:
    "norm (slp_cauchy_transform SLP_Partial_Inverse ?g z) \<le>
      norm (inverse (of_real pi :: complex)) *
        (M * (delta * (6 * integral\<^sup>L lborel
          (slp_localized_cauchy_kernel 1) + 2 * unit_ball_vol 2)))"
    by (rule order_trans[OF transform_to_majorant
          mult_left_mono[OF majorant_upper coefficient_nonnegative]])
  show ?thesis
    unfolding slp_partial_psi_inverse_eq
    using composed by (simp add: algebra_simps)
qed

end

end
