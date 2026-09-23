theory Inverse_Schrodinger_Lp_W1p_Rough_Far_Coefficient_Uniform
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_014.Inverse_Schrodinger_Lp_W1p_Rough_Far_Cutoff_Uniform"
begin

section \<open>Uniform output control of the far coefficient derivative\<close>

context slp_qstar_centered_smooth_far_hls_context
begin

theorem slp_w1p_global_far_coefficient_derivative_uniform_bound:
  fixes b A R delta tau :: real
    and X :: "slp_point set"
    and u :: slp_scalar_field
    and Du :: slp_gradient_field
    and c z :: slp_point
  assumes exponent_above_two: "2 < b"
    and radius_nonnegative: "0 \<le> A"
    and set_radius:
      "\<And>y :: slp_point. y \<in> X \<Longrightarrow>
        Real_Vector_Spaces.norm y \<le> A"
    and relative_radius:
      "\<And>y :: slp_point. y \<in> X \<Longrightarrow>
        Real_Vector_Spaces.norm (y - c) \<le> R"
    and delta_positive: "0 < delta"
    and normalized_lower: "1 \<le> R / delta"
    and zero_pair: "slp_w1p_zero_pair_on b X u Du"
  defines "q \<equiv> slp_holder_conjugate b"
  shows cauchy_integrable:
      "slp_cauchy_integrable_at SLP_Partial_Inverse
        (slp_oscillatory_modulation tau c
          (slp_w1p_global_far_coefficient_derivative_source
            delta c X u)) z"
    and coefficient_bound:
      "Real_Vector_Spaces.norm (slp_partial_psi_inverse tau c
          (slp_w1p_global_far_coefficient_derivative_source
            delta c X u) z) \<le>
        (((Real_Vector_Spaces.norm (inverse (of_real pi :: complex)) *
              slp_global_cutoff_L / delta) *
            ((Real_Vector_Spaces.norm (inverse (of_real pi :: complex)) *
              (integral\<^sup>L lborel
                (\<lambda>x. abs (slp_localized_cauchy_kernel (2 * A) x)
                  powr q)) powr (1 / q)) *
              (192 * slp_w1p_norm_on b X u Du))) *
          (6 * integral\<^sup>L lborel
              (slp_localized_cauchy_kernel 1) +
            2 * unit_ball_vol 2)) +
        Real_Vector_Spaces.norm (inverse (of_real pi :: complex)) *
          ((Real_Vector_Spaces.norm (inverse (of_real pi :: complex)) *
            (integral\<^sup>L lborel
              (\<lambda>x. abs (slp_localized_cauchy_kernel (2 * A) x)
                powr q)) powr (1 / q)) *
            (192 * slp_w1p_norm_on b X u Du)) *
          ((1 / delta) *
              integral\<^sup>L lborel (slp_localized_cauchy_kernel 1) +
            (1 / delta) * (1 + log 2 (R / delta)) *
              integral\<^sup>L lborel (slp_squared_radial_annulus 1 2))"
proof -
  let ?H =
    "slp_w1p_global_far_coefficient_derivative_source delta c X u"
  let ?C =
    "slp_w1p_global_far_cutoff_derivative_source delta c X u"
  let ?S =
    "slp_w1p_global_far_square_denominator_source delta c X u"
  let ?GH = "slp_oscillatory_modulation tau c ?H"
  let ?GC = "slp_oscillatory_modulation tau c ?C"
  let ?GS = "slp_oscillatory_modulation tau c ?S"
  let ?D = "\<lambda>y. - ?GC y - ?GS y"
  let ?P =
    "Real_Vector_Spaces.norm (inverse (of_real pi :: complex))"
  let ?M =
    "(?P *
      (integral\<^sup>L lborel
        (\<lambda>x. abs (slp_localized_cauchy_kernel (2 * A) x) powr q))
          powr (1 / q)) *
      (192 * slp_w1p_norm_on b X u Du)"
  let ?K =
    "6 * integral\<^sup>L lborel (slp_localized_cauchy_kernel 1) +
      2 * unit_ball_vol 2"
  let ?CB =
    "((?P * slp_global_cutoff_L / delta) * ?M) * ?K"
  let ?SB =
    "?P * ?M *
      ((1 / delta) *
          integral\<^sup>L lborel (slp_localized_cauchy_kernel 1) +
        (1 / delta) * (1 + log 2 (R / delta)) *
          integral\<^sup>L lborel (slp_squared_radial_annulus 1 2))"

  note cutoff =
    slp_w1p_global_far_cutoff_derivative_partial_psi_inverse_uniform_bound[
      OF exponent_above_two radius_nonnegative set_radius delta_positive
        zero_pair, folded q_def, where c=c and z=z]
  note square =
    slp_w1p_global_far_square_denominator_cauchy_logarithmic_bound[
      OF exponent_above_two radius_nonnegative set_radius relative_radius
        delta_positive normalized_lower zero_pair,
      folded q_def, where orientation=SLP_Partial_Inverse and z=z]
  have modulated_source: "?GH = ?D"
  proof (rule ext)
    fix y :: slp_point
    note source =
      slp_w1p_global_far_coefficient_derivative_source_pointwise[
        OF delta_positive, of c X u y]
    show "?GH y = ?D y"
      unfolding slp_oscillatory_modulation_def source
      by (simp add: algebra_simps)
  qed

  have cutoff_raw:
      "integrable lborel
        (slp_cauchy_integrand SLP_Partial_Inverse ?GC z)"
    using cutoff(1) unfolding slp_cauchy_integrable_at_def .
  have square_raw:
      "integrable lborel
        (slp_cauchy_integrand SLP_Partial_Inverse ?GS z)"
    using square(1) unfolding slp_cauchy_integrable_at_def .
  have negative_cutoff_raw:
      "integrable lborel
        (\<lambda>y. - slp_cauchy_integrand
          SLP_Partial_Inverse ?GC z y)"
    by (rule Bochner_Integration.integrable_minus[OF cutoff_raw])
  have combined_integrand:
      "slp_cauchy_integrand SLP_Partial_Inverse ?D z =
        (\<lambda>y. - slp_cauchy_integrand SLP_Partial_Inverse ?GC z y -
          slp_cauchy_integrand SLP_Partial_Inverse ?GS z y)"
    by (rule ext)
      (simp add: slp_cauchy_integrand_def algebra_simps)
  have combined_raw:
      "integrable lborel
        (slp_cauchy_integrand SLP_Partial_Inverse ?D z)"
    unfolding combined_integrand
    by (rule Bochner_Integration.integrable_diff[
          OF negative_cutoff_raw square_raw])
  have combined_cauchy:
      "slp_cauchy_integrable_at SLP_Partial_Inverse ?D z"
    unfolding slp_cauchy_integrable_at_def by (rule combined_raw)
  show "slp_cauchy_integrable_at SLP_Partial_Inverse ?GH z"
    unfolding modulated_source by (rule combined_cauchy)

  have combined_integral:
      "integral\<^sup>L lborel
          (slp_cauchy_integrand SLP_Partial_Inverse ?D z) =
        - integral\<^sup>L lborel
            (slp_cauchy_integrand SLP_Partial_Inverse ?GC z) -
          integral\<^sup>L lborel
            (slp_cauchy_integrand SLP_Partial_Inverse ?GS z)"
    unfolding combined_integrand
    by (simp only: Bochner_Integration.integral_diff[
          OF negative_cutoff_raw square_raw]
        Bochner_Integration.integral_minus)
  have combined_transform:
      "slp_cauchy_transform SLP_Partial_Inverse ?D z =
        - slp_cauchy_transform SLP_Partial_Inverse ?GC z -
          slp_cauchy_transform SLP_Partial_Inverse ?GS z"
    unfolding slp_cauchy_transform_def combined_integral
    by (simp add: algebra_simps)
  have exact_split:
      "slp_partial_psi_inverse tau c ?H z =
        - slp_partial_psi_inverse tau c ?C z -
          slp_partial_psi_inverse tau c ?S z"
    unfolding slp_partial_psi_inverse_eq modulated_source
    by (rule combined_transform)
  have triangle:
      "Real_Vector_Spaces.norm (slp_partial_psi_inverse tau c ?H z) \<le>
        Real_Vector_Spaces.norm (slp_partial_psi_inverse tau c ?C z) +
          Real_Vector_Spaces.norm (slp_partial_psi_inverse tau c ?S z)"
  proof -
    have raw_triangle:
        "Real_Vector_Spaces.norm
            (- slp_partial_psi_inverse tau c ?C z -
              slp_partial_psi_inverse tau c ?S z) \<le>
          Real_Vector_Spaces.norm
              (- slp_partial_psi_inverse tau c ?C z) +
            Real_Vector_Spaces.norm
              (slp_partial_psi_inverse tau c ?S z)"
      by (rule norm_triangle_ineq4)
    show ?thesis
      unfolding exact_split using raw_triangle by simp
  qed
  have cutoff_bound:
      "Real_Vector_Spaces.norm
          (slp_partial_psi_inverse tau c ?C z) \<le> ?CB"
    by (rule cutoff(2))
  have square_bound:
      "Real_Vector_Spaces.norm
          (slp_partial_psi_inverse tau c ?S z) \<le> ?SB"
    unfolding slp_partial_psi_inverse_eq by (rule square(2))
  have summed_bound:
      "Real_Vector_Spaces.norm
          (slp_partial_psi_inverse tau c ?C z) +
        Real_Vector_Spaces.norm
          (slp_partial_psi_inverse tau c ?S z) \<le> ?CB + ?SB"
    by (rule add_mono[OF cutoff_bound square_bound])
  show "Real_Vector_Spaces.norm
      (slp_partial_psi_inverse tau c ?H z) \<le> ?CB + ?SB"
    by (rule order_trans[OF triangle summed_bound])
qed

end

end
