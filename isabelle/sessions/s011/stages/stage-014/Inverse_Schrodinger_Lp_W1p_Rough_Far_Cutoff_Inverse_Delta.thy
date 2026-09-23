theory Inverse_Schrodinger_Lp_W1p_Rough_Far_Cutoff_Inverse_Delta
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_014.Inverse_Schrodinger_Lp_W1p_Rough_Far_Cutoff_Source_Cauchy"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_009.Inverse_Schrodinger_Lp_Localized_Cauchy_Power_Scaling"
begin

section \<open>Inverse-delta normalization of the rough cutoff contribution\<close>

lemma slp_w1p_cutoff_cauchy_ball_scale:
  fixes b delta P L M :: real
  assumes exponent_above_two: "2 < b"
    and delta_positive: "0 < delta"
  defines "q \<equiv> slp_holder_conjugate b"
  shows
    "(P *
        (integral\<^sup>L lborel
          (\<lambda>x. abs (slp_localized_cauchy_kernel (2 * delta) x)
            powr q)) powr (1 / q)) *
        (((L / delta ^ 2) * M) *
          (pi * (2 * delta) ^ 2) powr (1 / b)) =
      (2 * L / delta) *
        ((P *
          (integral\<^sup>L lborel
            (\<lambda>x. abs (slp_localized_cauchy_kernel 1 x) powr q))
              powr (1 / q)) *
          pi powr (1 / b) * M)"
proof -
  let ?R = "2 * delta"
  let ?J = "(integral\<^sup>L lborel
    (\<lambda>x. abs (slp_localized_cauchy_kernel 1 x) powr q))
      powr (1 / q)"
  have q_lower: "1 < q"
    and q_upper: "q < 2"
    and conjugates: "1 / q + 1 / b = 1"
    unfolding q_def
    using slp_holder_conjugate_arithmetic[OF exponent_above_two]
    by auto
  have q_at_least_one: "1 \<le> q"
    using q_lower by linarith
  have radius_positive: "0 < ?R"
    using delta_positive by simp
  have kernel_scale:
      "(integral\<^sup>L lborel
          (\<lambda>x. abs (slp_localized_cauchy_kernel ?R x) powr q))
          powr (1 / q) =
        ?R powr (2 / q - 1) * ?J"
    by (rule slp_localized_cauchy_kernel_power_root_scale[OF
          radius_positive q_at_least_one q_upper])
  have ball_scale_general:
      "(pi * R ^ 2) powr (1 / b) =
        pi powr (1 / b) * R powr (2 / b)"
    if R_positive: "0 < R" for R :: real
  proof -
    have square_as_powr: "R ^ 2 = R powr (real 2)"
      using R_positive by (simp add: powr_realpow)
    show ?thesis
      unfolding square_as_powr
      by (simp add: powr_mult powr_powr algebra_simps)
  qed
  have ball_scale:
      "(pi * ?R ^ 2) powr (1 / b) =
        pi powr (1 / b) * ?R powr (2 / b)"
    by (rule ball_scale_general[OF radius_positive])
  have exponent_balance: "(2 / q - 1) + 2 / b = 1"
    using conjugates by linarith
  have radius_product:
      "?R powr (2 / q - 1) * ?R powr (2 / b) = ?R"
  proof -
    have "?R powr (2 / q - 1) * ?R powr (2 / b) =
        ?R powr ((2 / q - 1) + 2 / b)"
      by (rule powr_add[symmetric])
    also have "... = ?R powr 1"
      by (simp only: exponent_balance)
    also have "... = ?R"
      using radius_positive by simp
    finally show ?thesis .
  qed
  have delta_nonzero: "delta \<noteq> 0"
    using delta_positive by simp
  show ?thesis
    unfolding kernel_scale ball_scale
    using radius_product delta_nonzero
    by (simp add: divide_inverse power2_eq_square algebra_simps)
qed

context slp_qstar_centered_smooth_far_hls_context
begin

theorem slp_w1p_global_far_cutoff_derivative_inverse_delta_bound:
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
    and inverse_delta_bound:
      "norm (slp_cauchy_transform orientation
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
  let ?P = "norm (inverse (of_real pi :: complex))"
  let ?M = "((?P *
    (integral\<^sup>L lborel
      (\<lambda>x. abs (slp_localized_cauchy_kernel (2 * A) x) powr q))
        powr (1 / q)) *
    (192 * slp_w1p_norm_on b X u Du))"
  note cauchy =
    slp_w1p_global_far_cutoff_derivative_source_cauchy_center[
      OF exponent_above_two radius_nonnegative set_radius delta_positive
        zero_pair, where orientation=orientation]
  show "slp_cauchy_integrable_at orientation ?S c"
    by (rule cauchy(1))
  have raw_bound:
      "norm (slp_cauchy_transform orientation ?S c) \<le>
        (?P *
          (integral\<^sup>L lborel
            (\<lambda>x. abs (slp_localized_cauchy_kernel (2 * delta) x)
              powr q)) powr (1 / q)) *
          (((slp_global_cutoff_L / delta ^ 2) * ?M) *
            (pi * (2 * delta) ^ 2) powr (1 / b))"
    unfolding q_def by (rule cauchy(2))
  have normalized_bound:
      "(?P *
          (integral\<^sup>L lborel
            (\<lambda>x. abs (slp_localized_cauchy_kernel (2 * delta) x)
              powr q)) powr (1 / q)) *
          (((slp_global_cutoff_L / delta ^ 2) * ?M) *
            (pi * (2 * delta) ^ 2) powr (1 / b)) =
        (2 * slp_global_cutoff_L / delta) *
          ((?P *
            (integral\<^sup>L lborel
              (\<lambda>x. abs (slp_localized_cauchy_kernel 1 x) powr q))
                powr (1 / q)) *
            pi powr (1 / b) * ?M)"
    unfolding q_def
    by (rule slp_w1p_cutoff_cauchy_ball_scale[OF exponent_above_two
          delta_positive])
  show "norm (slp_cauchy_transform orientation ?S c) \<le>
      (2 * slp_global_cutoff_L / delta) *
        ((?P *
          (integral\<^sup>L lborel
            (\<lambda>x. abs (slp_localized_cauchy_kernel 1 x) powr q))
              powr (1 / q)) *
          pi powr (1 / b) * ?M)"
    using raw_bound by (simp only: normalized_bound)
qed

end

end
