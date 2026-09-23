theory Inverse_Schrodinger_Lp_W1p_Rough_Near_Far_AE_Inverse_Sqrt_Bound
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_014.Inverse_Schrodinger_Lp_W1p_Rough_Near_Far_AE_Uniform_Bound"
begin

section \<open>Almost-everywhere arbitrary-output inverse-square-root control\<close>

context slp_qstar_centered_smooth_far_hls_context
begin

theorem slp_w1p_zero_pair_partial_psi_inverse_rough_AE_inverse_sqrt_bound:
  fixes b A R tau :: real
    and X :: "slp_point set"
    and u :: slp_scalar_field
    and Du :: slp_gradient_field
    and c :: slp_point
  assumes tau_lower: "2 \<le> tau"
    and exponent_above_two: "2 < b"
    and radius_nonnegative: "0 \<le> A"
    and radius_lower: "1 \<le> R"
    and set_radius:
      "\<And>y :: slp_point. y \<in> X \<Longrightarrow>
        Real_Vector_Spaces.norm y \<le> A"
    and relative_radius:
      "\<And>y :: slp_point. y \<in> X \<Longrightarrow>
        Real_Vector_Spaces.norm (y - c) \<le> R"
    and X_measurable: "X \<in> sets lborel"
    and zero_pair: "slp_w1p_zero_pair_on b X u Du"
  defines "q \<equiv> slp_holder_conjugate b"
  shows total_integrable:
      "\<And>z :: slp_point. z \<in> X \<Longrightarrow>
        slp_cauchy_integrable_at SLP_Partial_Inverse
          (slp_oscillatory_modulation tau c
            (slp_restrict_field X u)) z"
    and inverse_sqrt_bound:
      "(let
          P = Real_Vector_Spaces.norm
            (inverse (of_real pi :: complex));
          K = P *
            (integral\<^sup>L lborel
              (\<lambda>x. abs (slp_localized_cauchy_kernel (2 * A) x)
                powr q)) powr (1 / q);
          W = slp_w1p_norm_on b X u Du;
          M = K * (192 * W);
          C = 6 * integral\<^sup>L lborel
              (slp_localized_cauchy_kernel 1) +
            2 * unit_ball_vol 2;
          N0 = P * M * C;
          B0 = 2 * M;
          DB0 = K * (2 * (4 * W));
          CB0 = ((P * slp_global_cutoff_L) * M) * C;
          SB0 = P * M *
            (integral\<^sup>L lborel (slp_localized_cauchy_kernel 1) +
              (1 + log 2 (R * sqrt tau)) *
                integral\<^sup>L lborel
                  (slp_squared_radial_annulus 1 2))
        in
          AE z in lborel. z \<in> X \<longrightarrow>
            Real_Vector_Spaces.norm
              (slp_partial_psi_inverse tau c
                (slp_restrict_field X u) z) \<le>
            inverse (sqrt tau) *
              (N0 + (B0 + (DB0 + (CB0 + SB0)))))"
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
    slp_w1p_zero_pair_partial_psi_inverse_rough_AE_uniform_bound[
      where b=b and A=A and R=R and tau=tau and c=c and X=X
        and delta="inverse (sqrt tau)" and u=u and Du=Du,
      OF tau_positive exponent_above_two radius_nonnegative set_radius
        relative_radius X_measurable delta_positive normalized_lower zero_pair,
      folded q_def]
  show total_integrable:
      "\<And>z :: slp_point. z \<in> X \<Longrightarrow>
        slp_cauchy_integrable_at SLP_Partial_Inverse
          (slp_oscillatory_modulation tau c
            (slp_restrict_field X u)) z"
    by (rule base(1))

  let ?P =
    "Real_Vector_Spaces.norm (inverse (of_real pi :: complex))"
  let ?K =
    "?P *
      (integral\<^sup>L lborel
        (\<lambda>x. abs (slp_localized_cauchy_kernel (2 * A) x) powr q))
          powr (1 / q)"
  let ?W = "slp_w1p_norm_on b X u Du"
  let ?M = "?K * (192 * ?W)"
  let ?I = "integral\<^sup>L lborel (slp_localized_cauchy_kernel 1)"
  let ?J =
    "integral\<^sup>L lborel (slp_squared_radial_annulus 1 2)"
  let ?C = "6 * ?I + 2 * unit_ball_vol 2"
  let ?N0 = "?P * ?M * ?C"
  let ?B0 = "2 * ?M"
  let ?DB0 = "?K * (2 * (4 * ?W))"
  let ?CB0 = "((?P * slp_global_cutoff_L) * ?M) * ?C"
  let ?SB0 =
    "?P * ?M * (?I + (1 + log 2 (R * sqrt tau)) * ?J)"

  have raw_bound:
      "AE z in lborel. z \<in> X \<longrightarrow>
        Real_Vector_Spaces.norm
          (slp_partial_psi_inverse tau c
            (slp_restrict_field X u) z) \<le>
        ?P * ?M * inverse (sqrt tau) * ?C +
          (1 / tau) *
            ((2 / inverse (sqrt tau)) * ?M +
              (?K * ((2 / inverse (sqrt tau)) * (4 * ?W)) +
                (((?P * slp_global_cutoff_L /
                    inverse (sqrt tau)) * ?M) * ?C +
                  ?P * ?M *
                    ((1 / inverse (sqrt tau)) * ?I +
                      (1 / inverse (sqrt tau)) *
                        (1 + log 2
                          (R / inverse (sqrt tau))) * ?J))))"
    using base(2)
    unfolding Let_def by blast
  have root_ratio: "sqrt tau / tau = inverse (sqrt tau)"
    by (rule sqrt_divide_self_eq[OF tau_nonnegative])
  have scaled_root:
      "(1 / tau) * sqrt tau = inverse (sqrt tau)"
    using root_ratio by (simp add: divide_inverse algebra_simps)
  have normalization:
      "?P * ?M * inverse (sqrt tau) * ?C +
          (1 / tau) *
            ((2 / inverse (sqrt tau)) * ?M +
              (?K * ((2 / inverse (sqrt tau)) * (4 * ?W)) +
                (((?P * slp_global_cutoff_L /
                    inverse (sqrt tau)) * ?M) * ?C +
                  ?P * ?M *
                    ((1 / inverse (sqrt tau)) * ?I +
                      (1 / inverse (sqrt tau)) *
                        (1 + log 2
                          (R / inverse (sqrt tau))) * ?J)))) =
        inverse (sqrt tau) *
          (?N0 + (?B0 + (?DB0 + (?CB0 + ?SB0))))"
  proof -
    have substituted:
        "?P * ?M * inverse (sqrt tau) * ?C +
            (1 / tau) *
              ((2 / inverse (sqrt tau)) * ?M +
                (?K * ((2 / inverse (sqrt tau)) * (4 * ?W)) +
                  (((?P * slp_global_cutoff_L /
                      inverse (sqrt tau)) * ?M) * ?C +
                    ?P * ?M *
                      ((1 / inverse (sqrt tau)) * ?I +
                        (1 / inverse (sqrt tau)) *
                          (1 + log 2
                            (R / inverse (sqrt tau))) * ?J)))) =
          inverse (sqrt tau) * ?N0 +
            ((1 / tau) * sqrt tau) *
              (?B0 + (?DB0 + (?CB0 + ?SB0)))"
      by (simp add: divide_inverse algebra_simps)
    have combined:
        "inverse (sqrt tau) * ?N0 +
            ((1 / tau) * sqrt tau) *
              (?B0 + (?DB0 + (?CB0 + ?SB0))) =
          inverse (sqrt tau) *
            (?N0 + (?B0 + (?DB0 + (?CB0 + ?SB0))))"
    proof -
      have distribution:
          "inverse (sqrt tau) *
              (?N0 + (?B0 + (?DB0 + (?CB0 + ?SB0)))) =
            inverse (sqrt tau) * ?N0 +
              inverse (sqrt tau) *
                (?B0 + (?DB0 + (?CB0 + ?SB0)))"
        by (rule distrib_left)
      show ?thesis
        using distribution by (simp only: scaled_root)
    qed
    show ?thesis
      by (rule trans[OF substituted combined])
  qed
  show inverse_sqrt_bound:
      "(let
          P = Real_Vector_Spaces.norm
            (inverse (of_real pi :: complex));
          K = P *
            (integral\<^sup>L lborel
              (\<lambda>x. abs (slp_localized_cauchy_kernel (2 * A) x)
                powr q)) powr (1 / q);
          W = slp_w1p_norm_on b X u Du;
          M = K * (192 * W);
          C = 6 * integral\<^sup>L lborel
              (slp_localized_cauchy_kernel 1) +
            2 * unit_ball_vol 2;
          N0 = P * M * C;
          B0 = 2 * M;
          DB0 = K * (2 * (4 * W));
          CB0 = ((P * slp_global_cutoff_L) * M) * C;
          SB0 = P * M *
            (integral\<^sup>L lborel (slp_localized_cauchy_kernel 1) +
              (1 + log 2 (R * sqrt tau)) *
                integral\<^sup>L lborel
                  (slp_squared_radial_annulus 1 2))
        in
          AE z in lborel. z \<in> X \<longrightarrow>
            Real_Vector_Spaces.norm
              (slp_partial_psi_inverse tau c
                (slp_restrict_field X u) z) \<le>
            inverse (sqrt tau) *
              (N0 + (B0 + (DB0 + (CB0 + SB0)))))"
    unfolding Let_def
  proof (use raw_bound in eventually_elim)
    fix z :: slp_point
    assume pointwise:
      "z \<in> X \<longrightarrow>
        Real_Vector_Spaces.norm
          (slp_partial_psi_inverse tau c
            (slp_restrict_field X u) z) \<le>
        ?P * ?M * inverse (sqrt tau) * ?C +
          (1 / tau) *
            ((2 / inverse (sqrt tau)) * ?M +
              (?K * ((2 / inverse (sqrt tau)) * (4 * ?W)) +
                (((?P * slp_global_cutoff_L /
                    inverse (sqrt tau)) * ?M) * ?C +
                  ?P * ?M *
                    ((1 / inverse (sqrt tau)) * ?I +
                      (1 / inverse (sqrt tau)) *
                        (1 + log 2
                          (R / inverse (sqrt tau))) * ?J))))"
    show "z \<in> X \<longrightarrow>
        Real_Vector_Spaces.norm
          (slp_partial_psi_inverse tau c
            (slp_restrict_field X u) z) \<le>
        inverse (sqrt tau) *
          (?N0 + (?B0 + (?DB0 + (?CB0 + ?SB0))))"
    proof
      assume z_in: "z \<in> X"
      have "Real_Vector_Spaces.norm
          (slp_partial_psi_inverse tau c
            (slp_restrict_field X u) z) \<le>
          ?P * ?M * inverse (sqrt tau) * ?C +
            (1 / tau) *
              ((2 / inverse (sqrt tau)) * ?M +
                (?K * ((2 / inverse (sqrt tau)) * (4 * ?W)) +
                  (((?P * slp_global_cutoff_L /
                      inverse (sqrt tau)) * ?M) * ?C +
                    ?P * ?M *
                      ((1 / inverse (sqrt tau)) * ?I +
                        (1 / inverse (sqrt tau)) *
                          (1 + log 2
                            (R / inverse (sqrt tau))) * ?J))))"
        by (rule pointwise[THEN mp, OF z_in])
      also have "... = inverse (sqrt tau) *
          (?N0 + (?B0 + (?DB0 + (?CB0 + ?SB0))))"
        by (rule normalization)
      finally show "Real_Vector_Spaces.norm
          (slp_partial_psi_inverse tau c
            (slp_restrict_field X u) z) \<le>
        inverse (sqrt tau) *
          (?N0 + (?B0 + (?DB0 + (?CB0 + ?SB0))))" .
    qed
  qed
qed

end

end
