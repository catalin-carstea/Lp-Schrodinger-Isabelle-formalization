theory Inverse_Schrodinger_Lp_W1p_Rough_Far_Coefficient_Center
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_014.Inverse_Schrodinger_Lp_W1p_Rough_Far_Cutoff_Modulated"
begin

section \<open>Centered bound for the complete rough coefficient derivative\<close>

lemma slp_global_far_coefficient_wirtinger_center_zero:
  assumes delta_positive: "0 < delta"
  shows
    "slp_classical_wirtinger_partial
      (slp_global_far_coefficient delta c) c = 0"
proof -
  have coefficient_differentiable:
      "slp_global_far_coefficient delta c differentiable at c"
    using smooth_on_imp_differentiable_on[
        OF slp_global_far_coefficient_smooth[OF delta_positive]]
    by (simp add: differentiable_on_def)
  have center_ball: "c \<in> ball c delta"
    using delta_positive by simp
  have local_zero:
      "slp_global_far_coefficient delta c y =
        (\<lambda>_ :: slp_point. (0 :: complex)) y"
    if y_ball: "y \<in> ball c delta" for y
  proof -
    have y_inside_strict: "norm (y - c) < delta"
      using y_ball by (simp only: mem_ball dist_norm norm_minus_commute)
    have y_inside: "norm (y - c) \<le> delta"
      by (rule less_imp_le[OF y_inside_strict])
    have cutoff_one:
        "slp_global_cutoff.slp_scaled_cutoff delta c y = 1"
      by (rule slp_global_cutoff.slp_scaled_cutoff_inner[
            OF delta_positive y_inside])
    show ?thesis
      unfolding slp_global_far_coefficient_def
      by (simp only: cutoff_one diff_self of_real_0 mult_zero_left)
  qed
  have derivative_zero:
      "frechet_derivative (slp_global_far_coefficient delta c) (at c) =
        frechet_derivative (\<lambda>_ :: slp_point. (0 :: complex)) (at c)"
    by (rule frechet_derivative_transform_within_open[
          OF coefficient_differentiable open_ball center_ball local_zero])
  show ?thesis
    unfolding slp_classical_wirtinger_partial_frechet derivative_zero
      slp_complex_wirtinger_partial_def
    by simp
qed

theorem slp_w1p_global_far_coefficient_derivative_source_pointwise:
  assumes delta_positive: "0 < delta"
  shows
    "slp_w1p_global_far_coefficient_derivative_source delta c X u z =
      - slp_w1p_global_far_cutoff_derivative_source delta c X u z -
        slp_w1p_global_far_square_denominator_source delta c X u z"
proof (cases "z = c")
  case False
  show ?thesis
    by (rule slp_w1p_global_far_coefficient_derivative_source_away[OF False])
next
  case True
  have coefficient_zero:
      "slp_classical_wirtinger_partial
        (slp_global_far_coefficient delta c) c = 0"
    by (rule slp_global_far_coefficient_wirtinger_center_zero[
          OF delta_positive])
  have cutoff_one:
      "slp_global_cutoff.slp_scaled_cutoff delta c c = 1"
    by (rule slp_global_cutoff.slp_scaled_cutoff_inner[
          OF delta_positive])
      (use delta_positive in simp)
  have coordinate_zero: "slp_point_as_complex (c - c) = 0"
    by (rule iffD2[OF slp_point_as_complex_eq_zero_iff])
      (rule diff_self)
  show ?thesis
    unfolding True
      slp_w1p_global_far_coefficient_derivative_source_def
      slp_w1p_global_far_cutoff_derivative_source_def
      slp_w1p_global_far_square_denominator_source_def
      coefficient_zero cutoff_one coordinate_zero
    by (simp only: inverse_zero mult_zero_left mult_zero_right
        diff_self of_real_0 minus_zero diff_zero)
qed

context slp_qstar_centered_smooth_far_hls_context
begin

theorem slp_w1p_global_far_coefficient_derivative_center_bound:
  fixes b A R :: real
  assumes exponent_above_two: "2 < b"
    and radius_nonnegative: "0 \<le> A"
    and set_radius: "\<And>y. y \<in> X \<Longrightarrow> norm y \<le> A"
    and relative_radius: "\<And>y. y \<in> X \<Longrightarrow> norm (y - c) \<le> R"
    and delta_positive: "0 < delta"
    and normalized_lower: "1 \<le> R / delta"
    and zero_pair: "slp_w1p_zero_pair_on b X u Du"
  defines "q \<equiv> slp_holder_conjugate b"
  shows cauchy_integrable:
      "slp_cauchy_integrable_at SLP_Partial_Inverse
        (slp_oscillatory_modulation tau c
          (slp_w1p_global_far_coefficient_derivative_source delta c X u)) c"
    and coefficient_bound:
      "norm (slp_partial_psi_inverse tau c
          (slp_w1p_global_far_coefficient_derivative_source delta c X u) c)
        \<le>
        (2 * slp_global_cutoff_L / delta) *
          ((norm (inverse (of_real pi :: complex)) *
            (integral\<^sup>L lborel
              (\<lambda>x. abs (slp_localized_cauchy_kernel 1 x) powr q))
                powr (1 / q)) *
            pi powr (1 / b) *
            ((norm (inverse (of_real pi :: complex)) *
              (integral\<^sup>L lborel
                (\<lambda>x. abs (slp_localized_cauchy_kernel (2 * A) x)
                  powr q)) powr (1 / q)) *
              (192 * slp_w1p_norm_on b X u Du))) +
        norm (inverse (of_real pi :: complex)) *
          ((norm (inverse (of_real pi :: complex)) *
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
  let ?M =
    "(norm (inverse (of_real pi :: complex)) *
      (integral\<^sup>L lborel
        (\<lambda>x. abs (slp_localized_cauchy_kernel (2 * A) x) powr q))
          powr (1 / q)) *
      (192 * slp_w1p_norm_on b X u Du)"
  let ?CB =
    "(2 * slp_global_cutoff_L / delta) *
      ((norm (inverse (of_real pi :: complex)) *
        (integral\<^sup>L lborel
          (\<lambda>x. abs (slp_localized_cauchy_kernel 1 x) powr q))
            powr (1 / q)) *
        pi powr (1 / b) * ?M)"
  let ?SB =
    "norm (inverse (of_real pi :: complex)) * ?M *
      ((1 / delta) *
          integral\<^sup>L lborel (slp_localized_cauchy_kernel 1) +
        (1 / delta) * (1 + log 2 (R / delta)) *
          integral\<^sup>L lborel (slp_squared_radial_annulus 1 2))"

  note cutoff =
    slp_w1p_global_far_cutoff_derivative_partial_psi_inverse_delta_bound[
      OF exponent_above_two radius_nonnegative set_radius delta_positive
        zero_pair, folded q_def]
  note square =
    slp_w1p_global_far_square_denominator_cauchy_logarithmic_bound[
      OF exponent_above_two radius_nonnegative set_radius relative_radius
        delta_positive normalized_lower zero_pair,
      folded q_def, where orientation=SLP_Partial_Inverse and z=c]
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
        (slp_cauchy_integrand SLP_Partial_Inverse ?GC c)"
    using cutoff(1) unfolding slp_cauchy_integrable_at_def .
  have square_raw:
      "integrable lborel
        (slp_cauchy_integrand SLP_Partial_Inverse ?GS c)"
    using square(1) unfolding slp_cauchy_integrable_at_def .
  have negative_cutoff_raw:
      "integrable lborel
        (\<lambda>y. - slp_cauchy_integrand SLP_Partial_Inverse ?GC c y)"
    by (rule Bochner_Integration.integrable_minus[OF cutoff_raw])
  have combined_integrand:
      "slp_cauchy_integrand SLP_Partial_Inverse ?D c =
        (\<lambda>y. - slp_cauchy_integrand SLP_Partial_Inverse ?GC c y -
          slp_cauchy_integrand SLP_Partial_Inverse ?GS c y)"
    by (rule ext)
      (simp add: slp_cauchy_integrand_def algebra_simps)
  have combined_raw:
      "integrable lborel
        (slp_cauchy_integrand SLP_Partial_Inverse ?D c)"
    unfolding combined_integrand
    by (rule Bochner_Integration.integrable_diff[
          OF negative_cutoff_raw square_raw])
  have combined_cauchy:
      "slp_cauchy_integrable_at SLP_Partial_Inverse ?D c"
    unfolding slp_cauchy_integrable_at_def by (rule combined_raw)
  show "slp_cauchy_integrable_at SLP_Partial_Inverse ?GH c"
    unfolding modulated_source by (rule combined_cauchy)

  have combined_integral:
      "integral\<^sup>L lborel
          (slp_cauchy_integrand SLP_Partial_Inverse ?D c) =
        - integral\<^sup>L lborel
            (slp_cauchy_integrand SLP_Partial_Inverse ?GC c) -
          integral\<^sup>L lborel
            (slp_cauchy_integrand SLP_Partial_Inverse ?GS c)"
    unfolding combined_integrand
    by (simp only: Bochner_Integration.integral_diff[
          OF negative_cutoff_raw square_raw]
        Bochner_Integration.integral_minus)
  have combined_transform:
      "slp_cauchy_transform SLP_Partial_Inverse ?D c =
        - slp_cauchy_transform SLP_Partial_Inverse ?GC c -
          slp_cauchy_transform SLP_Partial_Inverse ?GS c"
    unfolding slp_cauchy_transform_def combined_integral
    by (simp add: algebra_simps)
  have exact_split:
      "slp_partial_psi_inverse tau c ?H c =
        - slp_partial_psi_inverse tau c ?C c -
          slp_partial_psi_inverse tau c ?S c"
    unfolding slp_partial_psi_inverse_eq modulated_source
    by (rule combined_transform)
  have triangle:
      "norm (slp_partial_psi_inverse tau c ?H c) \<le>
        norm (slp_partial_psi_inverse tau c ?C c) +
          norm (slp_partial_psi_inverse tau c ?S c)"
  proof -
    have raw_triangle:
        "norm (- slp_partial_psi_inverse tau c ?C c -
            slp_partial_psi_inverse tau c ?S c) \<le>
          norm (- slp_partial_psi_inverse tau c ?C c) +
            norm (slp_partial_psi_inverse tau c ?S c)"
      by (rule norm_triangle_ineq4)
    show ?thesis
      unfolding exact_split using raw_triangle by simp
  qed
  have cutoff_bound:
      "norm (slp_partial_psi_inverse tau c ?C c) \<le> ?CB"
    by (rule cutoff(2))
  have square_bound:
      "norm (slp_partial_psi_inverse tau c ?S c) \<le> ?SB"
    unfolding slp_partial_psi_inverse_eq by (rule square(2))
  have summed_bound:
      "norm (slp_partial_psi_inverse tau c ?C c) +
          norm (slp_partial_psi_inverse tau c ?S c) \<le> ?CB + ?SB"
    by (rule add_mono[OF cutoff_bound square_bound])
  show "norm (slp_partial_psi_inverse tau c ?H c) \<le> ?CB + ?SB"
    by (rule order_trans[OF triangle summed_bound])
qed

end

end
