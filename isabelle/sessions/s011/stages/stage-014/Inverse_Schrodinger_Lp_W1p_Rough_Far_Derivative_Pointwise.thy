theory Inverse_Schrodinger_Lp_W1p_Rough_Far_Derivative_Pointwise
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_014.Inverse_Schrodinger_Lp_W1p_Raw_Wirtinger_Derivative_Data"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_014.Inverse_Schrodinger_Lp_Cauchy_Bounded_Support_Pointwise"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_010.Inverse_Schrodinger_Lp_Qstar_Far_Amplitude_Derivative_Source"
begin

section \<open>The rough weak-derivative contribution to the far term\<close>

definition slp_w1p_global_far_derivative_source ::
    "real \<Rightarrow> slp_point \<Rightarrow> slp_point set \<Rightarrow>
      slp_gradient_field \<Rightarrow> slp_scalar_field"
where
  "slp_w1p_global_far_derivative_source delta c X Du z =
    slp_global_far_coefficient delta c z *
      slp_gradient_wirtinger_partial (slp_restrict_gradient X Du) z"

theorem slp_w1p_global_far_derivative_source_pointwise_bound:
  fixes b A :: real
  assumes exponent_above_two: "2 < b"
    and radius_nonnegative: "0 \<le> A"
    and set_radius: "\<And>y. y \<in> X \<Longrightarrow> norm y \<le> A"
    and output_in: "z \<in> X"
    and delta_positive: "0 < delta"
    and pair: "slp_w1p_pair_on b X u Du"
  defines "q \<equiv> slp_holder_conjugate b"
  shows source_lp:
      "aim_complex_lp_on_plane b
        (slp_w1p_global_far_derivative_source delta c X Du)"
    and output_bound:
      "norm (slp_partial_psi_inverse tau c
          (slp_w1p_global_far_derivative_source delta c X Du) z) \<le>
        (norm (inverse (of_real pi :: complex)) *
          (integral\<^sup>L lborel
            (\<lambda>x. abs (slp_localized_cauchy_kernel (2 * A) x) powr q))
              powr (1 / q)) *
          ((2 / delta) * (4 * slp_w1p_norm_on b X u Du))"
proof -
  have exponent_one_le: "1 \<le> b"
    and exponent_positive: "0 < b"
    using exponent_above_two by linarith+
  note partial = slp_w1p_restricted_gradient_wirtinger_partial_data[
    OF exponent_one_le pair]
  have coefficient_measurable:
      "slp_global_far_coefficient delta c \<in> borel_measurable lborel"
    by (rule slp_global_far_coefficient_borel_measurable[OF
          delta_positive])
  have coefficient_bound:
      "\<And>x. norm (slp_global_far_coefficient delta c x) \<le> 2 / delta"
    by (rule slp_global_far_coefficient_norm_bound[OF delta_positive])
  have coefficient_cap_nonnegative: "0 \<le> 2 / delta"
    using delta_positive by simp
  note product = slp_complex_lp_bounded_multiplier[
    OF exponent_positive coefficient_measurable coefficient_bound
      coefficient_cap_nonnegative partial(1)]
  have source_presentation:
      "slp_w1p_global_far_derivative_source delta c X Du =
        (\<lambda>x. slp_global_far_coefficient delta c x *
          slp_gradient_wirtinger_partial (slp_restrict_gradient X Du) x)"
    by (rule ext) (simp only: slp_w1p_global_far_derivative_source_def)
  show source_lp:
      "aim_complex_lp_on_plane b
        (slp_w1p_global_far_derivative_source delta c X Du)"
    unfolding source_presentation by (rule product(1))

  have source_norm_bound:
      "aim_complex_lp_norm b
          (slp_w1p_global_far_derivative_source delta c X Du) \<le>
        (2 / delta) * (4 * slp_w1p_norm_on b X u Du)"
  proof -
    have scaled_partial_bound:
        "(2 / delta) * aim_complex_lp_norm b
            (slp_gradient_wirtinger_partial (slp_restrict_gradient X Du))
          \<le> (2 / delta) * (4 * slp_w1p_norm_on b X u Du)"
      by (rule mult_left_mono[OF partial(2) coefficient_cap_nonnegative])
    have product_bound:
        "aim_complex_lp_norm b
            (slp_w1p_global_far_derivative_source delta c X Du) \<le>
          (2 / delta) * aim_complex_lp_norm b
            (slp_gradient_wirtinger_partial (slp_restrict_gradient X Du))"
      unfolding source_presentation by (rule product(2))
    show ?thesis
      by (rule order_trans[OF product_bound scaled_partial_bound])
  qed

  let ?h = "slp_w1p_global_far_derivative_source delta c X Du"
  let ?g = "slp_oscillatory_modulation tau c ?h"
  have modulated_lp: "aim_complex_lp_on_plane b ?g"
    using source_lp by simp
  have modulated_support:
      "?g y \<noteq> 0 \<Longrightarrow> norm (z - y) \<le> 2 * A" for y
  proof -
    assume modulated_nonzero: "?g y \<noteq> 0"
    have source_nonzero: "?h y \<noteq> 0"
    proof
      assume source_zero: "?h y = 0"
      show False
        using modulated_nonzero
        unfolding slp_oscillatory_modulation_def source_zero by simp
    qed
    have y_in: "y \<in> X"
      using source_nonzero
      unfolding slp_w1p_global_far_derivative_source_def
      by (cases "y \<in> X")
        (simp_all add: slp_gradient_wirtinger_partial_restrict_gradient
          slp_restrict_field_def)
    have z_bound: "norm z \<le> A"
      by (rule set_radius[OF output_in])
    have y_bound: "norm y \<le> A"
      by (rule set_radius[OF y_in])
    have triangle: "norm (z - y) \<le> norm z + norm y"
      by (rule norm_triangle_ineq4)
    show "norm (z - y) \<le> 2 * A"
      using triangle z_bound y_bound by linarith
  qed
  have doubled_radius_nonnegative: "0 \<le> 2 * A"
    using radius_nonnegative by simp
  note cauchy = slp_cauchy_transform_bounded_support_lp_pointwise[
    OF exponent_above_two doubled_radius_nonnegative modulated_lp
      modulated_support, where orientation=SLP_Partial_Inverse]
  let ?K = "norm (inverse (of_real pi :: complex)) *
    (integral\<^sup>L lborel
      (\<lambda>x. abs (slp_localized_cauchy_kernel (2 * A) x) powr q))
        powr (1 / q)"
  have coefficient_nonnegative: "0 \<le> ?K"
    by (rule mult_nonneg_nonneg) simp_all
  have transform_bound:
      "norm (slp_partial_psi_inverse tau c ?h z) \<le>
        ?K * aim_complex_lp_norm b ?h"
    unfolding slp_partial_psi_inverse_eq q_def
    using cauchy[THEN conjunct2] by simp
  have scaled_source_bound:
      "?K * aim_complex_lp_norm b ?h \<le>
        ?K * ((2 / delta) * (4 * slp_w1p_norm_on b X u Du))"
    by (rule mult_left_mono[OF source_norm_bound coefficient_nonnegative])
  show output_bound:
      "norm (slp_partial_psi_inverse tau c ?h z) \<le>
        ?K * ((2 / delta) * (4 * slp_w1p_norm_on b X u Du))"
    by (rule order_trans[OF transform_bound scaled_source_bound])
qed

end
