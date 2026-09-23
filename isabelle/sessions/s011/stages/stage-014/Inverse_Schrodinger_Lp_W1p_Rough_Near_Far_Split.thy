theory Inverse_Schrodinger_Lp_W1p_Rough_Near_Far_Split
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_014.Inverse_Schrodinger_Lp_W1p_Rough_Near_Essential_Bound"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_014.Inverse_Schrodinger_Lp_W1p_Rough_Global_Far_IBP"
begin

section \<open>Exact centered near/far splitting for a rough Sobolev field\<close>

lemma slp_w1p_global_far_modulated_source_eq:
  assumes delta_positive: "0 < delta"
  shows
    "(\<lambda>x. (slp_point_as_complex (x - c) *
        slp_center_kernel tau c x) *
      slp_restrict_field X
        (\<lambda>y. slp_global_far_coefficient delta c y * u y) x) =
    slp_oscillatory_modulation tau c
      (slp_global_far_cutoff_amplitude delta c
        (slp_restrict_field X u))"
proof (rule ext)
  fix x :: slp_point
  have restricted_at:
      "slp_restrict_field X
          (\<lambda>y. slp_global_far_coefficient delta c y * u y) x =
        slp_global_far_coefficient delta c x *
          slp_restrict_field X u x"
    by (simp add: slp_restrict_field_def)
  show "(slp_point_as_complex (x - c) * slp_center_kernel tau c x) *
        slp_restrict_field X
          (\<lambda>y. slp_global_far_coefficient delta c y * u y) x =
      slp_oscillatory_modulation tau c
        (slp_global_far_cutoff_amplitude delta c
          (slp_restrict_field X u)) x"
  proof (cases "x = c")
    case True
    have cutoff_one:
        "slp_global_cutoff.slp_scaled_cutoff delta c x = 1"
      unfolding True
      by (rule slp_global_cutoff.slp_scaled_cutoff_inner[
            OF delta_positive]) (use delta_positive in simp)
    have coordinate_zero: "slp_point_as_complex (x - c) = 0"
    proof (rule iffD2[OF slp_point_as_complex_eq_zero_iff])
      show "x - c = 0"
        unfolding True by (rule diff_self)
    qed
    show ?thesis
      apply (subst restricted_at)
      unfolding slp_global_far_coefficient_def
        slp_global_far_cutoff_amplitude_def
        slp_global_scaled_cutoff_def slp_oscillatory_modulation_def
      by (simp only: coordinate_zero cutoff_one diff_self of_real_0
            mult_zero_left mult_zero_right)
  next
    case False
    have difference_nonzero:
        "slp_point_as_complex (x - c) \<noteq> 0"
    proof
      assume zero: "slp_point_as_complex (x - c) = 0"
      then have "x - c = 0"
        by (simp only: slp_point_as_complex_eq_zero_iff)
      with False show False by simp
    qed
    have inverse_cancel:
        "slp_point_as_complex (x - c) *
            inverse (slp_point_as_complex (x - c)) = 1"
      by (rule right_inverse[OF difference_nonzero])
    have regroup:
        "(slp_point_as_complex (x - c) * slp_center_kernel tau c x) *
          (of_real (1 -
              slp_global_cutoff.slp_scaled_cutoff delta c x) *
            inverse (slp_point_as_complex (x - c)) *
            slp_restrict_field X u x) =
        (slp_center_kernel tau c x *
            (of_real (1 -
              slp_global_cutoff.slp_scaled_cutoff delta c x) *
              slp_restrict_field X u x)) *
          (slp_point_as_complex (x - c) *
            inverse (slp_point_as_complex (x - c)))"
      by (simp only: ac_simps)
    have algebra:
        "(slp_point_as_complex (x - c) * slp_center_kernel tau c x) *
          (of_real (1 -
              slp_global_cutoff.slp_scaled_cutoff delta c x) *
            inverse (slp_point_as_complex (x - c)) *
            slp_restrict_field X u x) =
        slp_center_kernel tau c x *
          (of_real (1 -
            slp_global_cutoff.slp_scaled_cutoff delta c x) *
            slp_restrict_field X u x)"
      by (rule trans[OF regroup])
        (simp only: inverse_cancel mult_1_right)
    show ?thesis
      apply (subst restricted_at)
      unfolding slp_global_far_coefficient_def
        slp_global_far_cutoff_amplitude_def
        slp_global_scaled_cutoff_def slp_oscillatory_modulation_def
      by (rule algebra)
  qed
qed

theorem slp_w1p_zero_pair_global_far_cauchy_integrable_center:
  fixes b R :: real
    and c :: slp_point
  assumes exponent_above_two: "2 < b"
    and radius_nonnegative: "0 \<le> R"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
    and relative_radius:
      "\<And>y. y \<in> X \<Longrightarrow> Real_Vector_Spaces.norm (c - y) \<le> R"
    and delta_positive: "0 < delta"
    and zero_pair: "slp_w1p_zero_pair_on b X u Du"
  shows
    "slp_cauchy_integrable_at SLP_Partial_Inverse
      (slp_oscillatory_modulation tau c
        (slp_global_far_cutoff_amplitude delta c
          (slp_restrict_field X u))) c"
proof -
  let ?v = "\<lambda>x. slp_global_far_coefficient delta c x * u x"
  let ?Dv = "\<lambda>x. \<chi> i.
    slp_global_far_coefficient delta c x * Du x $ i +
    u x * slp_complex_partial_derivative
      (slp_global_far_coefficient delta c) i x"
  have exponent_one_le: "1 \<le> b"
    using exponent_above_two by linarith
  have product_zero_pair: "slp_w1p_zero_pair_on b X ?v ?Dv"
    by (rule slp_w1p_zero_pair_on_global_far_coefficient[
          OF exponent_one_le X_measurable X_bounded delta_positive zero_pair])
  have product_pair: "slp_w1p_pair_on b X ?v ?Dv"
    using product_zero_pair unfolding slp_w1p_zero_pair_on_def by blast
  have source_integrable:
      "slp_cauchy_integrable_at SLP_Partial_Inverse
        (\<lambda>x. (slp_point_as_complex (x - c) *
          slp_center_kernel tau c x) * slp_restrict_field X ?v x) c"
    by (rule slp_w1p_rough_far_target_cauchy_integrable(1)[
          OF exponent_above_two radius_nonnegative product_pair
            relative_radius])
  have source_eq:
      "(\<lambda>x. (slp_point_as_complex (x - c) *
          slp_center_kernel tau c x) * slp_restrict_field X ?v x) =
        slp_oscillatory_modulation tau c
          (slp_global_far_cutoff_amplitude delta c
            (slp_restrict_field X u))"
    by (rule slp_w1p_global_far_modulated_source_eq[OF delta_positive])
  show ?thesis
    using source_integrable unfolding source_eq .
qed

context slp_qstar_centered_smooth_far_hls_context
begin

theorem slp_w1p_zero_pair_near_far_split_center:
  fixes b A R :: real
    and c :: slp_point
  assumes exponent_above_two: "2 < b"
    and radius_nonnegative: "0 \<le> A"
    and relative_radius_nonnegative: "0 \<le> R"
    and set_radius:
      "\<And>y. y \<in> X \<Longrightarrow> Real_Vector_Spaces.norm y \<le> A"
    and relative_radius:
      "\<And>y. y \<in> X \<Longrightarrow> Real_Vector_Spaces.norm (c - y) \<le> R"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
    and delta_positive: "0 < delta"
    and zero_pair: "slp_w1p_zero_pair_on b X u Du"
  shows total_integrable:
      "slp_cauchy_integrable_at SLP_Partial_Inverse
        (slp_oscillatory_modulation tau c
          (slp_restrict_field X u)) c"
    and operator_split:
      "slp_partial_psi_inverse tau c (slp_restrict_field X u) c =
        slp_partial_psi_inverse tau c
          (slp_global_cutoff.slp_near_cutoff_amplitude delta c
            (slp_restrict_field X u)) c +
        slp_partial_psi_inverse tau c
          (slp_global_far_cutoff_amplitude delta c
            (slp_restrict_field X u)) c"
proof -
  let ?f = "slp_restrict_field X u"
  let ?near =
    "slp_global_cutoff.slp_near_cutoff_amplitude delta c ?f"
  let ?far = "slp_global_far_cutoff_amplitude delta c ?f"
  have near_integrable:
      "slp_cauchy_integrable_at SLP_Partial_Inverse
        (slp_oscillatory_modulation tau c ?near) c"
    by (rule slp_w1p_zero_pair_near_center_bound(1)[
          OF exponent_above_two radius_nonnegative set_radius
            delta_positive zero_pair])
  have far_integrable:
      "slp_cauchy_integrable_at SLP_Partial_Inverse
        (slp_oscillatory_modulation tau c ?far) c"
    by (rule slp_w1p_zero_pair_global_far_cauchy_integrable_center[
          OF exponent_above_two relative_radius_nonnegative X_measurable
            X_bounded relative_radius delta_positive zero_pair])
  have amplitude_split: "?f = (\<lambda>y. ?near y + ?far y)"
  proof (rule ext)
    fix y :: slp_point
    show "?f y = ?near y + ?far y"
      unfolding slp_global_cutoff.slp_near_cutoff_amplitude_def
        slp_global_far_cutoff_amplitude_def slp_global_scaled_cutoff_def
      by (simp add: algebra_simps)
  qed
  have modulated_split:
      "slp_oscillatory_modulation tau c ?f =
        (\<lambda>y. slp_oscillatory_modulation tau c ?near y +
          slp_oscillatory_modulation tau c ?far y)"
  proof (rule ext)
    fix y :: slp_point
    have pointwise_split: "?f y = ?near y + ?far y"
      using fun_cong[OF amplitude_split, of y] .
    show "slp_oscillatory_modulation tau c ?f y =
        slp_oscillatory_modulation tau c ?near y +
          slp_oscillatory_modulation tau c ?far y"
      unfolding slp_oscillatory_modulation_def
      apply (subst pointwise_split)
      by (rule distrib_left)
  qed
  have sum_integrable:
      "slp_cauchy_integrable_at SLP_Partial_Inverse
        (\<lambda>y. slp_oscillatory_modulation tau c ?near y +
          slp_oscillatory_modulation tau c ?far y) c"
    by (rule slp_cauchy_integrable_at_add[OF near_integrable far_integrable])
  show "slp_cauchy_integrable_at SLP_Partial_Inverse
      (slp_oscillatory_modulation tau c ?f) c"
    apply (subst modulated_split)
    by (rule sum_integrable)
  have transform_split:
      "slp_cauchy_transform SLP_Partial_Inverse
          (\<lambda>y. slp_oscillatory_modulation tau c ?near y +
            slp_oscillatory_modulation tau c ?far y) c =
        slp_cauchy_transform SLP_Partial_Inverse
            (slp_oscillatory_modulation tau c ?near) c +
          slp_cauchy_transform SLP_Partial_Inverse
            (slp_oscillatory_modulation tau c ?far) c"
    by (rule slp_cauchy_transform_add[OF near_integrable far_integrable])
  show "slp_partial_psi_inverse tau c ?f c =
      slp_partial_psi_inverse tau c ?near c +
        slp_partial_psi_inverse tau c ?far c"
    apply (subst slp_partial_psi_inverse_eq)
    apply (subst slp_partial_psi_inverse_eq)
    apply (subst slp_partial_psi_inverse_eq)
    apply (subst modulated_split)
    by (rule transform_split)
qed

end

end
