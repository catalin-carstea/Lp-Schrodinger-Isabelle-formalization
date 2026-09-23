theory Inverse_Schrodinger_Lp_W1p_Rough_Far_Complete_Derivative_Uniform
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_014.Inverse_Schrodinger_Lp_W1p_Rough_Far_Coefficient_Uniform"
begin

section \<open>Complete uniform-output bound for the rough far derivative\<close>

context slp_qstar_centered_smooth_far_hls_context
begin

theorem slp_w1p_global_far_complete_derivative_uniform_bound:
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
    and output_in: "z \<in> X"
    and delta_positive: "0 < delta"
    and normalized_lower: "1 \<le> R / delta"
    and zero_pair: "slp_w1p_zero_pair_on b X u Du"
  defines "q \<equiv> slp_holder_conjugate b"
  shows complete_integrable:
      "slp_cauchy_integrable_at SLP_Partial_Inverse
        (slp_oscillatory_modulation tau c
          (slp_restrict_field X
            (slp_gradient_wirtinger_partial
              (\<lambda>x. \<chi> i.
                slp_global_far_coefficient delta c x * Du x $ i +
                u x * slp_complex_partial_derivative
                  (slp_global_far_coefficient delta c) i x)))) z"
    and complete_bound:
      "Real_Vector_Spaces.norm (slp_partial_psi_inverse tau c
          (slp_restrict_field X
            (slp_gradient_wirtinger_partial
              (\<lambda>x. \<chi> i.
                slp_global_far_coefficient delta c x * Du x $ i +
                u x * slp_complex_partial_derivative
                  (slp_global_far_coefficient delta c) i x))) z) \<le>
        (Real_Vector_Spaces.norm (inverse (of_real pi :: complex)) *
          (integral\<^sup>L lborel
            (\<lambda>x. abs (slp_localized_cauchy_kernel (2 * A) x)
              powr q)) powr (1 / q)) *
          ((2 / delta) * (4 * slp_w1p_norm_on b X u Du)) +
        ((((Real_Vector_Spaces.norm (inverse (of_real pi :: complex)) *
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
              integral\<^sup>L lborel (slp_squared_radial_annulus 1 2)))"
proof -
  have pair: "slp_w1p_pair_on b X u Du"
    using zero_pair unfolding slp_w1p_zero_pair_on_def by blast
  let ?D = "slp_w1p_global_far_derivative_source delta c X Du"
  let ?H =
    "slp_w1p_global_far_coefficient_derivative_source delta c X u"
  let ?F =
    "slp_restrict_field X
      (slp_gradient_wirtinger_partial
        (\<lambda>x. \<chi> i.
          slp_global_far_coefficient delta c x * Du x $ i +
          u x * slp_complex_partial_derivative
            (slp_global_far_coefficient delta c) i x))"
  let ?GD = "slp_oscillatory_modulation tau c ?D"
  let ?GH = "slp_oscillatory_modulation tau c ?H"
  let ?GF = "slp_oscillatory_modulation tau c ?F"
  let ?P =
    "Real_Vector_Spaces.norm (inverse (of_real pi :: complex))"
  let ?K =
    "?P *
      (integral\<^sup>L lborel
        (\<lambda>x. abs (slp_localized_cauchy_kernel (2 * A) x) powr q))
          powr (1 / q)"
  let ?W = "slp_w1p_norm_on b X u Du"
  let ?DB = "?K * ((2 / delta) * (4 * ?W))"
  let ?M = "?K * (192 * ?W)"
  let ?C =
    "6 * integral\<^sup>L lborel (slp_localized_cauchy_kernel 1) +
      2 * unit_ball_vol 2"
  let ?CB = "((?P * slp_global_cutoff_L / delta) * ?M) * ?C"
  let ?SB =
    "?P * ?M *
      ((1 / delta) *
          integral\<^sup>L lborel (slp_localized_cauchy_kernel 1) +
        (1 / delta) * (1 + log 2 (R / delta)) *
          integral\<^sup>L lborel (slp_squared_radial_annulus 1 2))"

  note derivative = slp_w1p_global_far_derivative_source_pointwise_bound[
    OF exponent_above_two radius_nonnegative set_radius output_in
      delta_positive pair, folded q_def]
  note coefficient =
    slp_w1p_global_far_coefficient_derivative_uniform_bound[
      OF exponent_above_two radius_nonnegative set_radius relative_radius
        delta_positive normalized_lower zero_pair,
      folded q_def, where z=z]

  have modulated_lp: "aim_complex_lp_on_plane b ?GD"
    using derivative(1) by simp
  have modulated_support:
      "?GD y \<noteq> 0 \<Longrightarrow>
        Real_Vector_Spaces.norm (z - y) \<le> 2 * A" for y
  proof -
    assume modulated_nonzero: "?GD y \<noteq> 0"
    have source_nonzero: "?D y \<noteq> 0"
    proof
      assume source_zero: "?D y = 0"
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
    have z_bound: "Real_Vector_Spaces.norm z \<le> A"
      by (rule set_radius[OF output_in])
    have y_bound: "Real_Vector_Spaces.norm y \<le> A"
      by (rule set_radius[OF y_in])
    have triangle:
        "Real_Vector_Spaces.norm (z - y) \<le>
          Real_Vector_Spaces.norm z + Real_Vector_Spaces.norm y"
      by (rule norm_triangle_ineq4)
    show "Real_Vector_Spaces.norm (z - y) \<le> 2 * A"
      using triangle z_bound y_bound by linarith
  qed
  have doubled_radius_nonnegative: "0 \<le> 2 * A"
    using radius_nonnegative by simp
  note derivative_cauchy =
    slp_cauchy_transform_bounded_support_lp_pointwise[
      OF exponent_above_two doubled_radius_nonnegative modulated_lp
        modulated_support,
      where orientation=SLP_Partial_Inverse, folded q_def]
  have derivative_integrable:
      "slp_cauchy_integrable_at SLP_Partial_Inverse ?GD z"
    by (rule conjunct1[OF derivative_cauchy])

  have source_split: "?F = (\<lambda>y. ?D y + ?H y)"
    by (rule slp_w1p_global_far_product_derivative_split)
  have modulated_split: "?GF = (\<lambda>y. ?GD y + ?GH y)"
  proof (rule ext)
    fix y :: slp_point
    show "?GF y = ?GD y + ?GH y"
      unfolding source_split slp_oscillatory_modulation_def
      by (simp add: algebra_simps)
  qed
  have sum_integrable:
      "slp_cauchy_integrable_at SLP_Partial_Inverse
        (\<lambda>y. ?GD y + ?GH y) z"
    by (rule slp_cauchy_integrable_at_add[
          OF derivative_integrable coefficient(1)])
  show "slp_cauchy_integrable_at SLP_Partial_Inverse ?GF z"
    unfolding modulated_split by (rule sum_integrable)

  have transform_add:
      "slp_cauchy_transform SLP_Partial_Inverse
          (\<lambda>y. ?GD y + ?GH y) z =
        slp_cauchy_transform SLP_Partial_Inverse ?GD z +
          slp_cauchy_transform SLP_Partial_Inverse ?GH z"
    by (rule slp_cauchy_transform_add[
          OF derivative_integrable coefficient(1)])
  have inverse_add:
      "slp_partial_psi_inverse tau c ?F z =
        slp_partial_psi_inverse tau c ?D z +
          slp_partial_psi_inverse tau c ?H z"
    unfolding slp_partial_psi_inverse_eq modulated_split
    by (rule transform_add)
  have triangle:
      "Real_Vector_Spaces.norm
          (slp_partial_psi_inverse tau c ?F z) \<le>
        Real_Vector_Spaces.norm
            (slp_partial_psi_inverse tau c ?D z) +
          Real_Vector_Spaces.norm
            (slp_partial_psi_inverse tau c ?H z)"
    unfolding inverse_add by (rule norm_triangle_ineq)
  have derivative_bound:
      "Real_Vector_Spaces.norm
          (slp_partial_psi_inverse tau c ?D z) \<le> ?DB"
    by (rule derivative(2))
  have coefficient_bound:
      "Real_Vector_Spaces.norm
          (slp_partial_psi_inverse tau c ?H z) \<le> ?CB + ?SB"
    by (rule coefficient(2))
  have summed_bound:
      "Real_Vector_Spaces.norm
          (slp_partial_psi_inverse tau c ?D z) +
        Real_Vector_Spaces.norm
          (slp_partial_psi_inverse tau c ?H z) \<le>
        ?DB + (?CB + ?SB)"
    by (rule add_mono[OF derivative_bound coefficient_bound])
  show "Real_Vector_Spaces.norm
      (slp_partial_psi_inverse tau c ?F z) \<le>
      ?DB + (?CB + ?SB)"
    by (rule order_trans[OF triangle summed_bound])
qed

end

end
