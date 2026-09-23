theory Inverse_Schrodinger_Lp_W1p_Rough_Far_Cutoff_Source_Cauchy
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_014.Inverse_Schrodinger_Lp_W1p_Rough_Far_Cutoff_Source_Lp"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_014.Inverse_Schrodinger_Lp_Cauchy_Bounded_Support_Pointwise"
begin

section \<open>Centered Cauchy control of the rough cutoff source\<close>

context slp_qstar_centered_smooth_far_hls_context
begin

theorem slp_w1p_global_far_cutoff_derivative_source_cauchy_center:
  fixes b A :: real
  assumes exponent_above_two: "2 < b"
    and radius_nonnegative: "0 \<le> A"
    and set_radius: "\<And>y. y \<in> X \<Longrightarrow> norm y \<le> A"
    and delta_positive: "0 < delta"
    and zero_pair: "slp_w1p_zero_pair_on b X u Du"
  defines "q \<equiv> slp_holder_conjugate b"
  shows cauchy_integrable:
      "slp_cauchy_integrable_at orientation
        (slp_w1p_global_far_cutoff_derivative_source delta c X u) c"
    and cauchy_norm_bound:
      "norm (slp_cauchy_transform orientation
          (slp_w1p_global_far_cutoff_derivative_source delta c X u) c) \<le>
        (norm (inverse (of_real pi :: complex)) *
          (integral\<^sup>L lborel
            (\<lambda>x. abs (slp_localized_cauchy_kernel (2 * delta) x)
              powr q)) powr (1 / q)) *
        (((slp_global_cutoff_L / delta ^ 2) *
          ((norm (inverse (of_real pi :: complex)) *
            (integral\<^sup>L lborel
              (\<lambda>x. abs (slp_localized_cauchy_kernel (2 * A) x)
                powr q)) powr (1 / q)) *
            (192 * slp_w1p_norm_on b X u Du))) *
          (pi * (2 * delta) ^ 2) powr (1 / b))"
proof -
  let ?S =
    "slp_w1p_global_far_cutoff_derivative_source delta c X u"
  let ?C = "norm (inverse (of_real pi :: complex)) *
    (integral\<^sup>L lborel
      (\<lambda>x. abs (slp_localized_cauchy_kernel (2 * delta) x) powr q))
        powr (1 / q)"
  let ?B = "((slp_global_cutoff_L / delta ^ 2) *
    ((norm (inverse (of_real pi :: complex)) *
      (integral\<^sup>L lborel
        (\<lambda>x. abs (slp_localized_cauchy_kernel (2 * A) x) powr q))
          powr (1 / q)) *
      (192 * slp_w1p_norm_on b X u Du))) *
    (pi * (2 * delta) ^ 2) powr (1 / b)"
  have source_lp: "aim_complex_lp_on_plane b ?S"
    by (rule slp_w1p_global_far_cutoff_derivative_source_lp_bound(1)[OF
          exponent_above_two radius_nonnegative set_radius delta_positive
          zero_pair])
  have source_norm: "aim_complex_lp_norm b ?S \<le> ?B"
    unfolding q_def
    by (rule slp_w1p_global_far_cutoff_derivative_source_lp_bound(2)[OF
          exponent_above_two radius_nonnegative set_radius delta_positive
          zero_pair])
  have source_support:
      "\<And>y. ?S y \<noteq> 0 \<Longrightarrow> norm (c - y) \<le> 2 * delta"
  proof -
    fix y :: slp_point
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
        "delta \<le> norm (y - c) \<and> norm (y - c) \<le> 2 * delta"
      using slp_cutoff_profile.slp_scaled_cutoff_partial_support[OF
          slp_global_cutoff_profile_spec[THEN conjunct1]
          delta_positive derivative_nonzero]
      by simp
    show "norm (c - y) \<le> 2 * delta"
      using annulus by (simp only: norm_minus_commute)
  qed
  have doubled_radius_nonnegative: "0 \<le> 2 * delta"
    using delta_positive by simp
  note cauchy = slp_cauchy_transform_bounded_support_lp_pointwise[
    OF exponent_above_two doubled_radius_nonnegative source_lp source_support,
      where orientation=orientation]
  show "slp_cauchy_integrable_at orientation ?S c"
    unfolding q_def by (rule cauchy[THEN conjunct1])
  have raw_bound:
      "norm (slp_cauchy_transform orientation ?S c) \<le>
        ?C * aim_complex_lp_norm b ?S"
    unfolding q_def by (rule cauchy[THEN conjunct2])
  have coefficient_nonnegative: "0 \<le> ?C"
    by (rule mult_nonneg_nonneg) simp_all
  have propagated_bound:
      "?C * aim_complex_lp_norm b ?S \<le> ?C * ?B"
    by (rule mult_left_mono[OF source_norm coefficient_nonnegative])
  show "norm (slp_cauchy_transform orientation ?S c) \<le> ?C * ?B"
    by (rule order_trans[OF raw_bound propagated_bound])
qed

end

end
