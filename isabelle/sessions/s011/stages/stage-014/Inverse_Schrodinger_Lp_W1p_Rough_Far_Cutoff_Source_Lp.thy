theory Inverse_Schrodinger_Lp_W1p_Rough_Far_Cutoff_Source_Lp
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_014.Inverse_Schrodinger_Lp_W1p_Rough_Far_Coefficient_Expansion"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_014.Inverse_Schrodinger_Lp_W1p_Zero_AE_Pointwise_Bound"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_012.Inverse_Schrodinger_Lp_Bounded_Support_Lp_Norm"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_010.Inverse_Schrodinger_Lp_Qstar_Centered_Cutoff_Source_Input_Lp"
begin

section \<open>Shrinking-support Lp control of the rough cutoff source\<close>

context slp_qstar_centered_smooth_far_hls_context
begin

theorem slp_w1p_global_far_cutoff_derivative_source_lp_bound:
  fixes b A :: real
  assumes exponent_above_two: "2 < b"
    and radius_nonnegative: "0 \<le> A"
    and set_radius: "\<And>y. y \<in> X \<Longrightarrow> norm y \<le> A"
    and delta_positive: "0 < delta"
    and zero_pair: "slp_w1p_zero_pair_on b X u Du"
  defines "q \<equiv> slp_holder_conjugate b"
  shows source_lp:
      "aim_complex_lp_on_plane b
        (slp_w1p_global_far_cutoff_derivative_source delta c X u)"
    and source_norm_bound:
      "aim_complex_lp_norm b
          (slp_w1p_global_far_cutoff_derivative_source delta c X u) \<le>
        ((slp_global_cutoff_L / delta ^ 2) *
          ((norm (inverse (of_real pi :: complex)) *
            (integral\<^sup>L lborel
              (\<lambda>x. abs (slp_localized_cauchy_kernel (2 * A) x)
                powr q)) powr (1 / q)) *
            (192 * slp_w1p_norm_on b X u Du))) *
          (pi * (2 * delta) ^ 2) powr (1 / b)"
proof -
  let ?S =
    "slp_w1p_global_far_cutoff_derivative_source delta c X u"
  let ?Y = "cball c (2 * delta)"
  let ?I = "slp_restrict_field ?Y (\<lambda>_. (1 :: complex))"
  let ?K = "norm (inverse (of_real pi :: complex)) *
    (integral\<^sup>L lborel
      (\<lambda>x. abs (slp_localized_cauchy_kernel (2 * A) x) powr q))
        powr (1 / q)"
  let ?M = "?K * (192 * slp_w1p_norm_on b X u Du)"
  let ?B = "(slp_global_cutoff_L / delta ^ 2) * ?M"

  have exponent_positive: "0 < b"
    using exponent_above_two by linarith
  have restricted_lp:
      "aim_complex_lp_on_plane b (slp_restrict_field X u)"
    using zero_pair
    unfolding slp_w1p_zero_pair_on_def slp_w1p_pair_on_def
      slp_complex_lp_on_def
    by blast
  have amplitude_measurable:
      "slp_restrict_field X u \<in> borel_measurable lborel"
    using restricted_lp unfolding aim_complex_lp_on_plane_def by blast
  have source_measurable: "?S \<in> borel_measurable lborel"
    unfolding slp_w1p_global_far_cutoff_derivative_source_def
    using slp_qstar_cutoff_partial_coefficient_borel_measurable[of delta c]
      amplitude_measurable
    apply measurable
    subgoal using slp_point_as_complex_borel_measurable by measurable
    subgoal by (rule amplitude_measurable)
    done

  have K_nonnegative: "0 \<le> ?K"
    by (rule mult_nonneg_nonneg) simp_all
  have rough_norm_nonnegative:
      "0 \<le> slp_w1p_norm_on b X u Du"
    unfolding slp_w1p_norm_on_def by simp
  have M_nonnegative: "0 \<le> ?M"
    by (rule mult_nonneg_nonneg[OF K_nonnegative])
      (rule mult_nonneg_nonneg, simp_all add: rough_norm_nonnegative)
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
      "AE y in lborel. norm (slp_restrict_field X u y) \<le> ?M"
    unfolding q_def
    by (rule slp_w1p_zero_pair_AE_pointwise_bound_on_bounded_set[
          OF exponent_above_two radius_nonnegative set_radius zero_pair])

  have source_support: "?S y \<noteq> 0 \<Longrightarrow> y \<in> ?Y" for y
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
        "delta \<le> norm (y - c) \<and> norm (y - c) \<le> 2 * delta"
      using slp_cutoff_profile.slp_scaled_cutoff_partial_support[OF
          slp_global_cutoff_profile_spec[THEN conjunct1]
          delta_positive derivative_nonzero]
      by simp
    show "y \<in> ?Y"
      using annulus by (simp add: dist_norm norm_minus_commute)
  qed

  have source_bound_AE: "AE y in lborel. norm (?S y) \<le> ?B"
  proof (use amplitude_bound in eventually_elim)
    fix y :: slp_point
    assume amplitude_at:
        "norm (slp_restrict_field X u y) \<le> ?M"
    let ?D = "slp_real_wirtinger_partial
      (slp_global_cutoff.slp_scaled_cutoff_derivative delta c y)"
    show "norm (?S y) \<le> ?B"
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
          "delta \<le> norm (y - c) \<and> norm (y - c) \<le> 2 * delta"
        using slp_cutoff_profile.slp_scaled_cutoff_partial_support[OF
            slp_global_cutoff_profile_spec[THEN conjunct1]
            delta_positive False]
        by simp
      have coefficient_bound:
          "norm (?D * inverse (slp_point_as_complex (y - c))) \<le>
            slp_global_cutoff_L / delta ^ 2"
        by (rule slp_global_cutoff.slp_far_cutoff_derivative_coefficient_bound[
              OF delta_positive annulus[THEN conjunct1]])
      have source_norm:
          "norm (?S y) =
            norm (?D * inverse (slp_point_as_complex (y - c))) *
              norm (slp_restrict_field X u y)"
        unfolding slp_w1p_global_far_cutoff_derivative_source_def
        by (simp only: norm_mult mult.assoc)
      have first_bound:
          "norm (?D * inverse (slp_point_as_complex (y - c))) *
              norm (slp_restrict_field X u y) \<le>
            (slp_global_cutoff_L / delta ^ 2) *
              norm (slp_restrict_field X u y)"
        by (rule mult_right_mono[OF coefficient_bound norm_ge_zero])
      have second_bound:
          "(slp_global_cutoff_L / delta ^ 2) *
              norm (slp_restrict_field X u y) \<le> ?B"
        by (rule mult_left_mono[OF amplitude_at cutoff_cap_nonnegative])
      show ?thesis
        unfolding source_norm
        by (rule order_trans[OF first_bound second_bound])
    qed
  qed

  have Y_measurable: "?Y \<in> sets (lborel :: slp_point measure)"
    by measurable
  have Y_bounded: "bounded ?Y"
    by (rule bounded_cball)
  have indicator_lp: "aim_complex_lp_on_plane b ?I"
    by (rule slp_complex_indicator_lp_norm(1)[OF exponent_positive
          Y_measurable Y_bounded])
  have indicator_norm:
      "aim_complex_lp_norm b ?I = measure lborel ?Y powr (1 / b)"
    by (rule slp_complex_indicator_lp_norm(2)[OF exponent_positive
          Y_measurable Y_bounded])
  have indicator_measurable: "?I \<in> borel_measurable lborel"
    unfolding slp_restrict_field_def using Y_measurable by measurable
  have indicator_norm_measurable:
      "(\<lambda>y. norm (?I y)) \<in> borel_measurable lborel"
    using indicator_measurable by measurable
  have indicator_norm_power_integrable:
      "integrable lborel (\<lambda>y. abs (norm (?I y)) powr b)"
    using indicator_lp unfolding aim_complex_lp_on_plane_def by simp
  have indicator_real_lp:
      "aim_real_lp_on_plane b (\<lambda>y. norm (?I y))"
    unfolding aim_real_lp_on_plane_def
    using indicator_norm_measurable indicator_norm_power_integrable by blast
  note majorant_scale = slp_nonnegative_real_lp_scale[
    OF exponent_positive B_nonnegative indicator_real_lp]
  have majorant_lp:
      "aim_real_lp_on_plane b (\<lambda>y. ?B * norm (?I y))"
    by (rule majorant_scale(1))
  have source_majorized:
      "AE y in lborel. norm (?S y) \<le> ?B * norm (?I y)"
  proof (use source_bound_AE in eventually_elim)
    fix y :: slp_point
    assume source_bound: "norm (?S y) \<le> ?B"
    show "norm (?S y) \<le> ?B * norm (?I y)"
    proof (cases "y \<in> ?Y")
      case True
      show ?thesis
        using source_bound
        unfolding slp_restrict_field_def if_P[OF True]
        by simp
    next
      case False
      have source_zero: "?S y = 0"
      proof (rule ccontr)
        assume "?S y \<noteq> 0"
        then have "y \<in> ?Y" by (rule source_support)
        with False show False by contradiction
      qed
      show ?thesis
        unfolding source_zero slp_restrict_field_def if_not_P[OF False]
        by simp
    qed
  qed
  note source_data = slp_complex_lp_real_majorant[
    OF exponent_positive source_measurable majorant_lp source_majorized]
  show "aim_complex_lp_on_plane b ?S"
    by (rule source_data(1))

  have majorant_norm:
      "aim_real_lp_norm b (\<lambda>y. ?B * norm (?I y)) =
        ?B * aim_complex_lp_norm b ?I"
  proof -
    have scaled:
        "aim_real_lp_norm b (\<lambda>y. ?B * norm (?I y)) =
          ?B * aim_real_lp_norm b (\<lambda>y. norm (?I y))"
      by (rule majorant_scale(2))
    have norm_identity:
        "aim_real_lp_norm b (\<lambda>y. norm (?I y)) =
          aim_complex_lp_norm b ?I"
      unfolding aim_real_lp_norm_def aim_complex_lp_norm_def by simp
    show ?thesis
      unfolding scaled norm_identity by (rule refl)
  qed
  have ball_measure: "measure lborel ?Y = pi * (2 * delta) ^ 2"
    using content_cball[where c=c and r="2 * delta"] delta_positive
    by (simp add: content_def unit_ball_vol_2)
  have final_majorant:
      "aim_real_lp_norm b (\<lambda>y. ?B * norm (?I y)) =
        ?B * (pi * (2 * delta) ^ 2) powr (1 / b)"
    unfolding majorant_norm indicator_norm ball_measure by (rule refl)
  show
      "aim_complex_lp_norm b ?S \<le>
        ((slp_global_cutoff_L / delta ^ 2) *
          ((norm (inverse (of_real pi :: complex)) *
            (integral\<^sup>L lborel
              (\<lambda>x. abs (slp_localized_cauchy_kernel (2 * A) x)
                powr q)) powr (1 / q)) *
            (192 * slp_w1p_norm_on b X u Du))) *
          (pi * (2 * delta) ^ 2) powr (1 / b)"
    using source_data(2) final_majorant by linarith
qed

end

end
