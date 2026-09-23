theory Inverse_Schrodinger_Lp_W1p_Rough_Center_Inverse_Sqrt_Bound
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_014.Inverse_Schrodinger_Lp_W1p_Rough_Center_Quantitative_Bound"
begin

section \<open>Inverse-square-root specialization at the phase center\<close>

context slp_qstar_centered_smooth_far_hls_context
begin

theorem slp_w1p_zero_pair_partial_psi_inverse_rough_center_inverse_sqrt_bound:
  fixes b A R tau :: real
    and c :: slp_point
    and X :: "slp_point set"
    and u :: slp_scalar_field
    and Du :: slp_gradient_field
  assumes tau_lower: "2 \<le> tau"
    and exponent_above_two: "2 < b"
    and radius_nonnegative: "0 \<le> A"
    and radius_lower: "1 \<le> R"
    and set_radius:
      "\<And>y. y \<in> X \<Longrightarrow> Real_Vector_Spaces.norm y \<le> A"
    and relative_radius:
      "\<And>y. y \<in> X \<Longrightarrow>
        Real_Vector_Spaces.norm (c - y) \<le> R"
    and center_in: "c \<in> X"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
    and zero_pair: "slp_w1p_zero_pair_on b X u Du"
  defines "q \<equiv> slp_holder_conjugate b"
  shows total_integrable:
      "slp_cauchy_integrable_at SLP_Partial_Inverse
        (slp_oscillatory_modulation tau c
          (slp_restrict_field X u)) c"
    and inverse_sqrt_bound:
      "(let
          P = Real_Vector_Spaces.norm (inverse (of_real pi :: complex));
          K = P *
            (integral\<^sup>L lborel
              (\<lambda>x. abs (slp_localized_cauchy_kernel (2 * A) x) powr q))
                powr (1 / q);
          K1 = P *
            (integral\<^sup>L lborel
              (\<lambda>x. abs (slp_localized_cauchy_kernel 1 x) powr q))
                powr (1 / q);
          W = slp_w1p_norm_on b X u Du;
          M = K * (192 * W);
          N0 = P * M *
            (6 * integral\<^sup>L lborel (slp_localized_cauchy_kernel 1) +
              2 * unit_ball_vol 2);
          DB0 = K * (2 * (4 * W));
          CB0 = (2 * slp_global_cutoff_L) *
            (K1 * pi powr (1 / b) * M);
          SB0 = P * M *
            (integral\<^sup>L lborel (slp_localized_cauchy_kernel 1) +
              (1 + log 2 (R * sqrt tau)) *
                integral\<^sup>L lborel
                  (slp_squared_radial_annulus 1 2))
        in
          Real_Vector_Spaces.norm (slp_partial_psi_inverse tau c
            (slp_restrict_field X u) c) \<le>
            inverse (sqrt tau) * (N0 + (DB0 + (CB0 + SB0))))"
proof -
  have tau_positive: "0 < tau"
    using tau_lower by linarith
  have tau_nonnegative: "0 \<le> tau"
    using tau_positive by linarith
  have relative_radius_nonnegative: "0 \<le> R"
    using radius_lower by linarith
  have delta_positive: "0 < inverse (sqrt tau)"
    using tau_positive by simp
  have sqrt_lower: "1 \<le> sqrt tau"
    by (rule real_sqrt_ge_one) (use tau_lower in linarith)
  have normalized_product: "1 \<le> R * sqrt tau"
  proof -
    have radius_growth: "R \<le> R * sqrt tau"
    proof -
      have "R * 1 \<le> R * sqrt tau"
        by (rule mult_left_mono[OF sqrt_lower
              relative_radius_nonnegative])
      then show ?thesis by simp
    qed
    show ?thesis
      by (rule order_trans[OF radius_lower radius_growth])
  qed
  have normalized_lower:
      "1 \<le> R / inverse (sqrt tau)"
    using normalized_product by (simp add: divide_inverse)

  note base =
    slp_w1p_zero_pair_partial_psi_inverse_rough_center_bound[
      where b=b and A=A and R=R and tau=tau and c=c and X=X
        and delta="inverse (sqrt tau)" and u=u and Du=Du,
      OF tau_positive exponent_above_two radius_nonnegative
        relative_radius_nonnegative set_radius relative_radius center_in
        X_measurable X_bounded delta_positive normalized_lower zero_pair,
      folded q_def]
  show total_integrable:
      "slp_cauchy_integrable_at SLP_Partial_Inverse
        (slp_oscillatory_modulation tau c
          (slp_restrict_field X u)) c"
    by (rule base(1))

  let ?P =
    "Real_Vector_Spaces.norm (inverse (of_real pi :: complex))"
  let ?K =
    "?P *
      (integral\<^sup>L lborel
        (\<lambda>x. abs (slp_localized_cauchy_kernel (2 * A) x) powr q))
          powr (1 / q)"
  let ?K1 =
    "?P *
      (integral\<^sup>L lborel
        (\<lambda>x. abs (slp_localized_cauchy_kernel 1 x) powr q))
          powr (1 / q)"
  let ?W = "slp_w1p_norm_on b X u Du"
  let ?M = "?K * (192 * ?W)"
  let ?I = "integral\<^sup>L lborel (slp_localized_cauchy_kernel 1)"
  let ?J =
    "integral\<^sup>L lborel (slp_squared_radial_annulus 1 2)"
  let ?N0 = "?P * ?M * (6 * ?I + 2 * unit_ball_vol 2)"
  let ?DB0 = "?K * (2 * (4 * ?W))"
  let ?CB0 =
    "(2 * slp_global_cutoff_L) *
      (?K1 * pi powr (1 / b) * ?M)"
  let ?SB0 =
    "?P * ?M * (?I + (1 + log 2 (R * sqrt tau)) * ?J)"

  have raw_bound:
      "Real_Vector_Spaces.norm (slp_partial_psi_inverse tau c
          (slp_restrict_field X u) c) \<le>
        ?P * ?M * inverse (sqrt tau) *
            (6 * ?I + 2 * unit_ball_vol 2) +
          (1 / tau) *
            (?K * ((2 / inverse (sqrt tau)) * (4 * ?W)) +
              (((2 * slp_global_cutoff_L) /
                    inverse (sqrt tau)) *
                  (?K1 * pi powr (1 / b) * ?M) +
                ?P * ?M *
                  ((1 / inverse (sqrt tau)) * ?I +
                    (1 / inverse (sqrt tau)) *
                      (1 + log 2 (R / inverse (sqrt tau))) * ?J)))"
    using base(2)
    unfolding Let_def by blast
  have root_ratio: "sqrt tau / tau = inverse (sqrt tau)"
    by (rule sqrt_divide_self_eq[OF tau_nonnegative])
  have scaled_root:
      "(1 / tau) * sqrt tau = inverse (sqrt tau)"
    using root_ratio by (simp add: divide_inverse algebra_simps)
  have normalization:
      "?P * ?M * inverse (sqrt tau) *
            (6 * ?I + 2 * unit_ball_vol 2) +
          (1 / tau) *
            (?K * ((2 / inverse (sqrt tau)) * (4 * ?W)) +
              (((2 * slp_global_cutoff_L) /
                    inverse (sqrt tau)) *
                  (?K1 * pi powr (1 / b) * ?M) +
                ?P * ?M *
                  ((1 / inverse (sqrt tau)) * ?I +
                    (1 / inverse (sqrt tau)) *
                      (1 + log 2 (R / inverse (sqrt tau))) * ?J))) =
        inverse (sqrt tau) * (?N0 + (?DB0 + (?CB0 + ?SB0)))"
  proof -
    have substituted:
        "?P * ?M * inverse (sqrt tau) *
              (6 * ?I + 2 * unit_ball_vol 2) +
            (1 / tau) *
              (?K * ((2 / inverse (sqrt tau)) * (4 * ?W)) +
                (((2 * slp_global_cutoff_L) /
                      inverse (sqrt tau)) *
                    (?K1 * pi powr (1 / b) * ?M) +
                  ?P * ?M *
                    ((1 / inverse (sqrt tau)) * ?I +
                      (1 / inverse (sqrt tau)) *
                        (1 + log 2 (R / inverse (sqrt tau))) * ?J))) =
          inverse (sqrt tau) * ?N0 +
            ((1 / tau) * sqrt tau) *
              (?DB0 + (?CB0 + ?SB0))"
      by (simp add: divide_inverse algebra_simps)
    have combined:
        "inverse (sqrt tau) * ?N0 +
            ((1 / tau) * sqrt tau) *
              (?DB0 + (?CB0 + ?SB0)) =
          inverse (sqrt tau) *
            (?N0 + (?DB0 + (?CB0 + ?SB0)))"
    proof -
      have distribution:
          "inverse (sqrt tau) *
              (?N0 + (?DB0 + (?CB0 + ?SB0))) =
            inverse (sqrt tau) * ?N0 +
              inverse (sqrt tau) *
                (?DB0 + (?CB0 + ?SB0))"
        by (rule distrib_left)
      show ?thesis
        using distribution by (simp only: scaled_root)
    qed
    show ?thesis
      by (rule trans[OF substituted combined])
  qed
  show inverse_sqrt_bound:
      "(let
          P = Real_Vector_Spaces.norm (inverse (of_real pi :: complex));
          K = P *
            (integral\<^sup>L lborel
              (\<lambda>x. abs (slp_localized_cauchy_kernel (2 * A) x) powr q))
                powr (1 / q);
          K1 = P *
            (integral\<^sup>L lborel
              (\<lambda>x. abs (slp_localized_cauchy_kernel 1 x) powr q))
                powr (1 / q);
          W = slp_w1p_norm_on b X u Du;
          M = K * (192 * W);
          N0 = P * M *
            (6 * integral\<^sup>L lborel (slp_localized_cauchy_kernel 1) +
              2 * unit_ball_vol 2);
          DB0 = K * (2 * (4 * W));
          CB0 = (2 * slp_global_cutoff_L) *
            (K1 * pi powr (1 / b) * M);
          SB0 = P * M *
            (integral\<^sup>L lborel (slp_localized_cauchy_kernel 1) +
              (1 + log 2 (R * sqrt tau)) *
                integral\<^sup>L lborel
                  (slp_squared_radial_annulus 1 2))
        in
          Real_Vector_Spaces.norm (slp_partial_psi_inverse tau c
            (slp_restrict_field X u) c) \<le>
            inverse (sqrt tau) * (N0 + (DB0 + (CB0 + SB0))))"
    unfolding Let_def
    using raw_bound normalization by linarith
qed

end

end
