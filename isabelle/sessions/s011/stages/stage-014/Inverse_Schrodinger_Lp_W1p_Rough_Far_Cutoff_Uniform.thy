theory Inverse_Schrodinger_Lp_W1p_Rough_Far_Cutoff_Uniform
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_014.Inverse_Schrodinger_Lp_W1p_Rough_Center_Natural_Log_Bound"
begin

section \<open>Uniform output control of the rough cutoff source\<close>

context slp_qstar_centered_smooth_far_hls_context
begin

theorem
  slp_w1p_global_far_cutoff_derivative_partial_psi_inverse_uniform_bound:
  fixes b A delta tau :: real
    and X :: "slp_point set"
    and u :: slp_scalar_field
    and Du :: slp_gradient_field
    and c z :: slp_point
  assumes exponent_above_two: "2 < b"
    and radius_nonnegative: "0 \<le> A"
    and set_radius:
      "\<And>y :: slp_point. y \<in> X \<Longrightarrow>
        Real_Vector_Spaces.norm y \<le> A"
    and delta_positive: "0 < delta"
    and zero_pair: "slp_w1p_zero_pair_on b X u Du"
  defines "q \<equiv> slp_holder_conjugate b"
  shows cauchy_integrable:
      "slp_cauchy_integrable_at SLP_Partial_Inverse
        (slp_oscillatory_modulation tau c
          (slp_w1p_global_far_cutoff_derivative_source delta c X u)) z"
    and inverse_delta_bound:
      "Real_Vector_Spaces.norm (slp_partial_psi_inverse tau c
          (slp_w1p_global_far_cutoff_derivative_source delta c X u) z) \<le>
        ((Real_Vector_Spaces.norm (inverse (of_real pi :: complex)) *
            slp_global_cutoff_L / delta) *
          ((Real_Vector_Spaces.norm (inverse (of_real pi :: complex)) *
            (integral\<^sup>L lborel
              (\<lambda>x. abs (slp_localized_cauchy_kernel (2 * A) x)
                powr q)) powr (1 / q)) *
            (192 * slp_w1p_norm_on b X u Du))) *
          (6 * integral\<^sup>L lborel
              (slp_localized_cauchy_kernel 1) +
            2 * unit_ball_vol 2)"
proof -
  let ?S =
    "slp_w1p_global_far_cutoff_derivative_source delta c X u"
  let ?G = "slp_oscillatory_modulation tau c ?S"
  let ?P = "Real_Vector_Spaces.norm (inverse (of_real pi :: complex))"
  let ?M =
    "(?P *
      (integral\<^sup>L lborel
        (\<lambda>x. abs (slp_localized_cauchy_kernel (2 * A) x) powr q))
          powr (1 / q)) *
      (192 * slp_w1p_norm_on b X u Du)"
  let ?B = "(slp_global_cutoff_L / delta ^ 2) * ?M"
  let ?H = "slp_near_center_scalar_kernel delta c z"
  let ?C =
    "6 * integral\<^sup>L lborel (slp_localized_cauchy_kernel 1) +
      2 * unit_ball_vol 2"

  have source_lp: "aim_complex_lp_on_plane b ?S"
    by (rule slp_w1p_global_far_cutoff_derivative_source_lp_bound(1)[OF
          exponent_above_two radius_nonnegative set_radius delta_positive
          zero_pair])
  have source_measurable: "?S \<in> borel_measurable lborel"
    using source_lp unfolding aim_complex_lp_on_plane_def by blast
  have modulated_measurable: "?G \<in> borel_measurable lborel"
    by (rule slp_oscillatory_modulation_measurable[OF source_measurable])

  have M_nonnegative: "0 \<le> ?M"
    unfolding slp_w1p_norm_on_def
    by (intro mult_nonneg_nonneg) simp_all
  have cutoff_nonnegative: "0 \<le> slp_global_cutoff_L"
    by (rule slp_global_cutoff_profile_spec[THEN conjunct2,
          THEN conjunct2, THEN conjunct1])
  have delta_square_positive: "0 < delta ^ 2"
    using delta_positive by simp
  have cutoff_cap_nonnegative:
      "0 \<le> slp_global_cutoff_L / delta ^ 2"
    by (rule divide_nonneg_pos[OF cutoff_nonnegative
          delta_square_positive])
  have B_nonnegative: "0 \<le> ?B"
    by (rule mult_nonneg_nonneg[OF cutoff_cap_nonnegative M_nonnegative])

  have amplitude_bound:
      "AE y in lborel.
        Real_Vector_Spaces.norm (slp_restrict_field X u y) \<le> ?M"
    unfolding q_def
    by (rule slp_w1p_zero_pair_AE_pointwise_bound_on_bounded_set[
          OF exponent_above_two radius_nonnegative set_radius zero_pair])

  have source_support:
      "?S y \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm (y - c) \<le> 2 * delta" for y
  proof -
    assume source_nonzero: "?S y \<noteq> 0"
    let ?D = "slp_real_wirtinger_partial
      (slp_global_cutoff.slp_scaled_cutoff_derivative delta c y)"
    have derivative_nonzero: "?D \<noteq> 0"
    proof
      assume derivative_zero: "?D = 0"
      have source_zero: "?S y = 0"
        unfolding slp_w1p_global_far_cutoff_derivative_source_def
          derivative_zero by (simp only: mult_zero_left)
      show False by (rule notE[OF source_nonzero source_zero])
    qed
    have annulus:
        "delta \<le> Real_Vector_Spaces.norm (y - c) \<and>
          Real_Vector_Spaces.norm (y - c) \<le> 2 * delta"
      using slp_cutoff_profile.slp_scaled_cutoff_partial_support[OF
          slp_global_cutoff_profile_spec[THEN conjunct1]
          delta_positive derivative_nonzero]
      by simp
    show "Real_Vector_Spaces.norm (y - c) \<le> 2 * delta"
      by (rule annulus[THEN conjunct2])
  qed

  have source_bound_AE:
      "AE y in lborel. Real_Vector_Spaces.norm (?S y) \<le> ?B"
  proof (use amplitude_bound in eventually_elim)
    fix y :: slp_point
    assume amplitude_at:
        "Real_Vector_Spaces.norm (slp_restrict_field X u y) \<le> ?M"
    let ?D = "slp_real_wirtinger_partial
      (slp_global_cutoff.slp_scaled_cutoff_derivative delta c y)"
    show "Real_Vector_Spaces.norm (?S y) \<le> ?B"
    proof (cases "?D = 0")
      case True
      have source_zero: "?S y = 0"
        unfolding slp_w1p_global_far_cutoff_derivative_source_def True
        by (simp only: mult_zero_left)
      show ?thesis
        unfolding source_zero norm_zero by (rule B_nonnegative)
    next
      case False
      have annulus:
          "delta \<le> Real_Vector_Spaces.norm (y - c) \<and>
            Real_Vector_Spaces.norm (y - c) \<le> 2 * delta"
        using slp_cutoff_profile.slp_scaled_cutoff_partial_support[OF
            slp_global_cutoff_profile_spec[THEN conjunct1]
            delta_positive False]
        by simp
      have coefficient_bound:
          "Real_Vector_Spaces.norm
              (?D * inverse (slp_point_as_complex (y - c))) \<le>
            slp_global_cutoff_L / delta ^ 2"
        by (rule slp_global_cutoff.slp_far_cutoff_derivative_coefficient_bound[
              OF delta_positive annulus[THEN conjunct1]])
      have source_norm:
          "Real_Vector_Spaces.norm (?S y) =
            Real_Vector_Spaces.norm
                (?D * inverse (slp_point_as_complex (y - c))) *
              Real_Vector_Spaces.norm (slp_restrict_field X u y)"
        unfolding slp_w1p_global_far_cutoff_derivative_source_def
        by (simp only: norm_mult mult.assoc)
      have first_bound:
          "Real_Vector_Spaces.norm
              (?D * inverse (slp_point_as_complex (y - c))) *
              Real_Vector_Spaces.norm (slp_restrict_field X u y) \<le>
            (slp_global_cutoff_L / delta ^ 2) *
              Real_Vector_Spaces.norm (slp_restrict_field X u y)"
        by (rule mult_right_mono[OF coefficient_bound norm_ge_zero])
      have second_bound:
          "(slp_global_cutoff_L / delta ^ 2) *
              Real_Vector_Spaces.norm (slp_restrict_field X u y) \<le> ?B"
        by (rule mult_left_mono[OF amplitude_at cutoff_cap_nonnegative])
      show ?thesis
        unfolding source_norm
        by (rule order_trans[OF first_bound second_bound])
    qed
  qed

  have integrand_bound:
      "AE y in lborel.
        Real_Vector_Spaces.norm
          (slp_cauchy_integrand SLP_Partial_Inverse ?G z y) \<le>
          ?B * ?H y"
  proof (use source_bound_AE in eventually_elim)
    fix y :: slp_point
    assume source_at: "Real_Vector_Spaces.norm (?S y) \<le> ?B"
    show "Real_Vector_Spaces.norm
          (slp_cauchy_integrand SLP_Partial_Inverse ?G z y) \<le>
        ?B * ?H y"
    proof (cases "Real_Vector_Spaces.norm (y - c) \<le> 2 * delta")
      case inside: True
      have scaled:
          "slp_radial_inverse (z - y) *
              Real_Vector_Spaces.norm (?S y) \<le>
            slp_radial_inverse (z - y) * ?B"
        by (rule mult_left_mono[OF source_at
              slp_radial_inverse_nonnegative])
      have integrand_norm:
          "Real_Vector_Spaces.norm
              (slp_cauchy_integrand SLP_Partial_Inverse ?G z y) =
            slp_radial_inverse (z - y) *
              Real_Vector_Spaces.norm (?S y)"
        unfolding slp_cauchy_integrand_def
        by (simp only: norm_mult slp_cauchy_kernel_norm
              slp_oscillatory_modulation_norm mult.commute)
      have kernel_value:
          "?H y = slp_radial_inverse (z - y)"
        unfolding slp_near_center_scalar_kernel_def
        by (simp only: if_P[OF inside])
      show ?thesis
        using scaled
        by (simp only: integrand_norm kernel_value mult.commute)
    next
      case outside: False
      have source_zero: "?S y = 0"
      proof (rule ccontr)
        assume source_nonzero: "?S y \<noteq> 0"
        have "Real_Vector_Spaces.norm (y - c) \<le> 2 * delta"
          by (rule source_support[OF source_nonzero])
        with outside show False by contradiction
      qed
      show ?thesis
        unfolding slp_cauchy_integrand_def
          slp_oscillatory_modulation_def source_zero
          slp_near_center_scalar_kernel_def
        using outside by simp
    qed
  qed

  have near_integrable: "integrable lborel ?H"
    by (rule slp_near_center_scalar_integrable[OF delta_positive])
  have majorant_integrable:
      "integrable lborel (\<lambda>y. ?B * ?H y)"
    by (rule integrable_mult_right[OF near_integrable])
  have cauchy_integrand_measurable:
      "slp_cauchy_integrand SLP_Partial_Inverse ?G z \<in>
        borel_measurable lborel"
    by (rule slp_cauchy_integrand_borel_measurable[OF
          modulated_measurable])
  have raw_integrable:
      "integrable lborel
        (slp_cauchy_integrand SLP_Partial_Inverse ?G z)"
  proof (rule Bochner_Integration.integrable_bound[OF majorant_integrable
        cauchy_integrand_measurable])
    show "AE y in lborel.
        Real_Vector_Spaces.norm
            (slp_cauchy_integrand SLP_Partial_Inverse ?G z y) \<le>
          Real_Vector_Spaces.norm (?B * ?H y)"
    proof (use integrand_bound in eventually_elim)
      fix y :: slp_point
      assume pointwise:
          "Real_Vector_Spaces.norm
              (slp_cauchy_integrand SLP_Partial_Inverse ?G z y) \<le>
            ?B * ?H y"
      have product_nonnegative: "0 \<le> ?B * ?H y"
        by (rule mult_nonneg_nonneg[OF B_nonnegative]) simp
      show "Real_Vector_Spaces.norm
            (slp_cauchy_integrand SLP_Partial_Inverse ?G z y) \<le>
          Real_Vector_Spaces.norm (?B * ?H y)"
        using pointwise
        by (simp only: real_norm_def abs_of_nonneg[OF product_nonnegative])
    qed
  qed
  show "slp_cauchy_integrable_at SLP_Partial_Inverse ?G z"
    unfolding slp_cauchy_integrable_at_def by (rule raw_integrable)

  have norm_integrable:
      "integrable lborel
        (\<lambda>y. Real_Vector_Spaces.norm
          (slp_cauchy_integrand SLP_Partial_Inverse ?G z y))"
    by (rule integrable_norm[OF raw_integrable])
  have integral_domination:
      "integral\<^sup>L lborel
          (\<lambda>y. Real_Vector_Spaces.norm
            (slp_cauchy_integrand SLP_Partial_Inverse ?G z y)) \<le>
        integral\<^sup>L lborel (\<lambda>y. ?B * ?H y)"
    by (rule integral_mono_AE[OF norm_integrable majorant_integrable
          integrand_bound])
  have majorant_integral:
      "integral\<^sup>L lborel (\<lambda>y. ?B * ?H y) =
        ?B * integral\<^sup>L lborel ?H"
    using near_integrable by simp
  have scalar_bound:
      "integral\<^sup>L lborel ?H \<le> delta * ?C"
    by (rule slp_near_center_scalar_integral_bound[OF delta_positive])
  have majorant_bound:
      "integral\<^sup>L lborel (\<lambda>y. ?B * ?H y) \<le>
        ?B * (delta * ?C)"
    using majorant_integral
      mult_left_mono[OF scalar_bound B_nonnegative]
    by simp

  have transform_raw:
      "Real_Vector_Spaces.norm
          (slp_cauchy_transform SLP_Partial_Inverse ?G z) \<le>
        ?P * integral\<^sup>L lborel
          (\<lambda>y. Real_Vector_Spaces.norm
            (slp_cauchy_integrand SLP_Partial_Inverse ?G z y))"
    by (rule slp_cauchy_transform_norm_bound)
  have P_nonnegative: "0 \<le> ?P"
    by simp
  have transform_to_majorant:
      "Real_Vector_Spaces.norm
          (slp_cauchy_transform SLP_Partial_Inverse ?G z) \<le>
        ?P * integral\<^sup>L lborel (\<lambda>y. ?B * ?H y)"
    by (rule order_trans[OF transform_raw
          mult_left_mono[OF integral_domination P_nonnegative]])
  have transform_bound:
      "Real_Vector_Spaces.norm
          (slp_cauchy_transform SLP_Partial_Inverse ?G z) \<le>
        ?P * (?B * (delta * ?C))"
    by (rule order_trans[OF transform_to_majorant
          mult_left_mono[OF majorant_bound P_nonnegative]])

  have delta_nonzero: "delta \<noteq> 0"
    using delta_positive by simp
  have quotient_cancel:
      "delta / delta ^ 2 = 1 / delta"
    using delta_nonzero
    by (simp add: power2_eq_square)
  have normalized:
      "?P * (?B * (delta * ?C)) =
        ((?P * slp_global_cutoff_L / delta) * ?M) * ?C"
  proof -
    have regroup:
        "?P * (?B * (delta * ?C)) =
          (((?P * slp_global_cutoff_L) *
              (delta / delta ^ 2)) * ?M) * ?C"
      by (simp add: divide_inverse; ring)
    have quotient_step:
        "(((?P * slp_global_cutoff_L) *
              (delta / delta ^ 2)) * ?M) * ?C =
          (((?P * slp_global_cutoff_L) *
              (1 / delta)) * ?M) * ?C"
      by (simp only: quotient_cancel)
    have division_step:
        "(((?P * slp_global_cutoff_L) *
              (1 / delta)) * ?M) * ?C =
          ((?P * slp_global_cutoff_L / delta) * ?M) * ?C"
      by (simp only: divide_inverse mult_1_left)
    show ?thesis
      by (rule trans[OF regroup trans[OF quotient_step division_step]])
  qed
  show "Real_Vector_Spaces.norm
        (slp_partial_psi_inverse tau c ?S z) \<le>
      ((?P * slp_global_cutoff_L / delta) * ?M) * ?C"
    unfolding slp_partial_psi_inverse_eq
    using transform_bound by (simp only: normalized)
qed

end

end
