theory Inverse_Schrodinger_Lp_W1p_Rough_Far_Cutoff_Modulated
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_014.Inverse_Schrodinger_Lp_W1p_Rough_Far_Square_Logarithmic"
begin

section \<open>Phase-modulated centered cutoff-source bound\<close>

context slp_qstar_centered_smooth_far_hls_context
begin

theorem slp_w1p_global_far_cutoff_derivative_partial_psi_inverse_delta_bound:
  fixes b A :: real
  assumes exponent_above_two: "2 < b"
    and radius_nonnegative: "0 \<le> A"
    and set_radius: "\<And>y. y \<in> X \<Longrightarrow> norm y \<le> A"
    and delta_positive: "0 < delta"
    and zero_pair: "slp_w1p_zero_pair_on b X u Du"
  defines "q \<equiv> slp_holder_conjugate b"
  shows cauchy_integrable:
      "slp_cauchy_integrable_at SLP_Partial_Inverse
        (slp_oscillatory_modulation tau c
          (slp_w1p_global_far_cutoff_derivative_source delta c X u)) c"
    and inverse_delta_bound:
      "norm (slp_partial_psi_inverse tau c
          (slp_w1p_global_far_cutoff_derivative_source delta c X u) c) \<le>
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
              (192 * slp_w1p_norm_on b X u Du)))"
proof -
  let ?S =
    "slp_w1p_global_far_cutoff_derivative_source delta c X u"
  let ?G = "slp_oscillatory_modulation tau c ?S"
  let ?P = "norm (inverse (of_real pi :: complex))"
  let ?M = "((?P *
    (integral\<^sup>L lborel
      (\<lambda>x. abs (slp_localized_cauchy_kernel (2 * A) x) powr q))
        powr (1 / q)) *
    (192 * slp_w1p_norm_on b X u Du))"
  let ?B = "((slp_global_cutoff_L / delta ^ 2) * ?M) *
    (pi * (2 * delta) ^ 2) powr (1 / b)"
  let ?C = "?P *
    (integral\<^sup>L lborel
      (\<lambda>x. abs (slp_localized_cauchy_kernel (2 * delta) x) powr q))
        powr (1 / q)"

  note source = slp_w1p_global_far_cutoff_derivative_source_lp_bound[
    OF exponent_above_two radius_nonnegative set_radius delta_positive
      zero_pair]
  have modulated_lp: "aim_complex_lp_on_plane b ?G"
    using source(1) by simp
  have modulated_norm_bound: "aim_complex_lp_norm b ?G \<le> ?B"
    unfolding q_def using source(2) by simp
  have modulated_support:
      "?G y \<noteq> 0 \<Longrightarrow> norm (c - y) \<le> 2 * delta" for y
  proof -
    assume modulated_nonzero: "?G y \<noteq> 0"
    have source_nonzero: "?S y \<noteq> 0"
    proof
      assume source_zero: "?S y = 0"
      show False
        using modulated_nonzero
        unfolding slp_oscillatory_modulation_def source_zero by simp
    qed
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
        "delta \<le> norm (y - c) \<and> norm (y - c) \<le> 2 * delta"
      using slp_cutoff_profile.slp_scaled_cutoff_partial_support[
          OF slp_global_cutoff_profile_spec[THEN conjunct1]
            delta_positive derivative_nonzero]
      by simp
    show "norm (c - y) \<le> 2 * delta"
      using annulus by (simp only: norm_minus_commute)
  qed

  have doubled_radius_nonnegative: "0 \<le> 2 * delta"
    using delta_positive by simp
  note cauchy = slp_cauchy_transform_bounded_support_lp_pointwise[
    OF exponent_above_two doubled_radius_nonnegative modulated_lp
      modulated_support, where orientation=SLP_Partial_Inverse]
  show "slp_cauchy_integrable_at SLP_Partial_Inverse ?G c"
    unfolding q_def by (rule cauchy[THEN conjunct1])
  have raw_bound:
      "norm (slp_cauchy_transform SLP_Partial_Inverse ?G c) \<le>
        ?C * aim_complex_lp_norm b ?G"
    unfolding q_def by (rule cauchy[THEN conjunct2])
  have coefficient_nonnegative: "0 \<le> ?C"
    by (rule mult_nonneg_nonneg) simp_all
  have propagated_bound:
      "?C * aim_complex_lp_norm b ?G \<le> ?C * ?B"
    by (rule mult_left_mono[OF modulated_norm_bound coefficient_nonnegative])
  have unnormalized_bound:
      "norm (slp_cauchy_transform SLP_Partial_Inverse ?G c) \<le> ?C * ?B"
    by (rule order_trans[OF raw_bound propagated_bound])
  have normalized_bound:
      "?C * ?B =
        (2 * slp_global_cutoff_L / delta) *
          ((?P *
            (integral\<^sup>L lborel
              (\<lambda>x. abs (slp_localized_cauchy_kernel 1 x) powr q))
                powr (1 / q)) *
            pi powr (1 / b) * ?M)"
    unfolding q_def
    by (rule slp_w1p_cutoff_cauchy_ball_scale[
          OF exponent_above_two delta_positive])
  show "norm (slp_partial_psi_inverse tau c ?S c) \<le>
      (2 * slp_global_cutoff_L / delta) *
        ((?P *
          (integral\<^sup>L lborel
            (\<lambda>x. abs (slp_localized_cauchy_kernel 1 x) powr q))
              powr (1 / q)) *
          pi powr (1 / b) * ?M)"
    unfolding slp_partial_psi_inverse_eq
    using unnormalized_bound by (simp only: normalized_bound)
qed

end

end
