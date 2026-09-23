theory Inverse_Schrodinger_Lp_W1p_Rough_Near_Far_AE_Natural_Log_Bound
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_015.Inverse_Schrodinger_Lp_W1p_Rough_Near_Far_AE_Inverse_Sqrt_Bound"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Natural_Logarithmic_Parameter_Comparison"
begin

section \<open>Almost-everywhere arbitrary-output natural-logarithmic control\<close>

context slp_qstar_centered_smooth_far_hls_context
begin

theorem slp_w1p_zero_pair_partial_psi_inverse_rough_AE_natural_log_bound:
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
    and natural_log_bound:
      "(let
          P = Real_Vector_Spaces.norm
            (inverse (of_real pi :: complex));
          K = P *
            (integral\<^sup>L lborel
              (\<lambda>x. abs (slp_localized_cauchy_kernel (2 * A) x)
                powr q)) powr (1 / q);
          W = slp_w1p_norm_on b X u Du;
          M = K * (192 * W);
          I = integral\<^sup>L lborel (slp_localized_cauchy_kernel 1);
          J = integral\<^sup>L lborel (slp_squared_radial_annulus 1 2);
          C = 6 * I + 2 * unit_ball_vol 2;
          N0 = P * M * C;
          B0 = 2 * M;
          DB0 = K * (2 * (4 * W));
          CB0 = ((P * slp_global_cutoff_L) * M) * C;
          C0 = N0 + (B0 + (DB0 + (CB0 + P * M * I)));
          C1 = P * M * J
        in
          AE z in lborel. z \<in> X \<longrightarrow>
            Real_Vector_Spaces.norm
              (slp_partial_psi_inverse tau c
                (slp_restrict_field X u) z) \<le>
            inverse (sqrt tau) * ln (2 + tau) *
              (C0 / ln 2 + C1 * ((2 + log 2 R) / ln 2)))"
proof -
  have tau_nonnegative: "0 \<le> tau"
    using tau_lower by linarith
  note base =
    slp_w1p_zero_pair_partial_psi_inverse_rough_AE_inverse_sqrt_bound[
      where b=b and A=A and R=R and tau=tau and c=c and X=X
        and u=u and Du=Du,
      OF tau_lower exponent_above_two radius_nonnegative radius_lower
        set_radius relative_radius X_measurable zero_pair,
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
  let ?H = "6 * ?I + 2 * unit_ball_vol 2"
  let ?N0 = "?P * ?M * ?H"
  let ?B0 = "2 * ?M"
  let ?DB0 = "?K * (2 * (4 * ?W))"
  let ?CB0 = "((?P * slp_global_cutoff_L) * ?M) * ?H"
  let ?C0 =
    "?N0 + (?B0 + (?DB0 + (?CB0 + ?P * ?M * ?I)))"
  let ?C1 = "?P * ?M * ?J"

  have raw_bound:
      "AE z in lborel. z \<in> X \<longrightarrow>
        Real_Vector_Spaces.norm
          (slp_partial_psi_inverse tau c
            (slp_restrict_field X u) z) \<le>
        inverse (sqrt tau) *
          (?N0 +
            (?B0 +
              (?DB0 +
                (?CB0 +
                  ?P * ?M *
                    (?I + (1 + log 2 (R * sqrt tau)) * ?J)))))"
    using base(2)
    unfolding Let_def by blast
  have regroup:
      "?N0 +
          (?B0 +
            (?DB0 +
              (?CB0 +
                ?P * ?M *
                  (?I + (1 + log 2 (R * sqrt tau)) * ?J)))) =
        ?C0 + ?C1 * (1 + log 2 (R * sqrt tau))"
    by (simp add: algebra_simps)
  have regrouped_bound:
      "AE z in lborel. z \<in> X \<longrightarrow>
        Real_Vector_Spaces.norm
          (slp_partial_psi_inverse tau c
            (slp_restrict_field X u) z) \<le>
        inverse (sqrt tau) *
          (?C0 + ?C1 * (1 + log 2 (R * sqrt tau)))"
    using raw_bound by (simp only: regroup)

  have P_nonnegative: "0 \<le> ?P"
    by simp
  have K_nonnegative: "0 \<le> ?K"
    by (rule mult_nonneg_nonneg[OF P_nonnegative]) simp
  have W_nonnegative: "0 \<le> ?W"
    unfolding slp_w1p_norm_on_def by simp
  have M_nonnegative: "0 \<le> ?M"
    by (rule mult_nonneg_nonneg[OF K_nonnegative])
       (rule mult_nonneg_nonneg, simp_all add: W_nonnegative)
  have I_nonnegative: "0 \<le> ?I"
    by (rule Bochner_Integration.integral_nonneg)
       (simp add: slp_localized_cauchy_kernel_nonnegative)
  have J_nonnegative: "0 \<le> ?J"
    by (rule Bochner_Integration.integral_nonneg) simp
  have H_nonnegative: "0 \<le> ?H"
    using I_nonnegative by simp
  have cutoff_nonnegative: "0 \<le> slp_global_cutoff_L"
    using slp_global_cutoff_profile_spec[THEN conjunct2, THEN conjunct2,
        THEN conjunct1] .
  have PM_nonnegative: "0 \<le> ?P * ?M"
    by (rule mult_nonneg_nonneg[OF P_nonnegative M_nonnegative])
  have N0_nonnegative: "0 \<le> ?N0"
    by (rule mult_nonneg_nonneg[OF PM_nonnegative H_nonnegative])
  have B0_nonnegative: "0 \<le> ?B0"
    using M_nonnegative by simp
  have DB0_nonnegative: "0 \<le> ?DB0"
    by (rule mult_nonneg_nonneg[OF K_nonnegative])
       (simp add: W_nonnegative)
  have cutoff_P_nonnegative:
      "0 \<le> ?P * slp_global_cutoff_L"
    by (rule mult_nonneg_nonneg[OF P_nonnegative cutoff_nonnegative])
  have cutoff_PM_nonnegative:
      "0 \<le> (?P * slp_global_cutoff_L) * ?M"
    by (rule mult_nonneg_nonneg[OF cutoff_P_nonnegative M_nonnegative])
  have CB0_nonnegative: "0 \<le> ?CB0"
    by (rule mult_nonneg_nonneg[OF cutoff_PM_nonnegative H_nonnegative])
  have PMI_nonnegative: "0 \<le> ?P * ?M * ?I"
    by (rule mult_nonneg_nonneg[OF PM_nonnegative I_nonnegative])
  have C0_tail_nonnegative: "0 \<le> ?CB0 + ?P * ?M * ?I"
    by (rule add_nonneg_nonneg[OF CB0_nonnegative PMI_nonnegative])
  have C0_derivative_nonnegative:
      "0 \<le> ?DB0 + (?CB0 + ?P * ?M * ?I)"
    by (rule add_nonneg_nonneg[OF DB0_nonnegative
          C0_tail_nonnegative])
  have C0_boundary_nonnegative:
      "0 \<le> ?B0 + (?DB0 + (?CB0 + ?P * ?M * ?I))"
    by (rule add_nonneg_nonneg[OF B0_nonnegative
          C0_derivative_nonnegative])
  have C0_nonnegative: "0 \<le> ?C0"
    by (rule add_nonneg_nonneg[OF N0_nonnegative
          C0_boundary_nonnegative])
  have C1_nonnegative: "0 \<le> ?C1"
    by (rule mult_nonneg_nonneg[OF PM_nonnegative J_nonnegative])

  note logarithmic = slp_log_sqrt_parameter_natural_bound[OF
      radius_lower tau_lower]
  have log_growth_at_least_one: "1 \<le> log 2 (2 + tau)"
  proof -
    have "log 2 2 \<le> log 2 (2 + tau)"
    proof (rule log_mono)
      show "(1::real) < 2" by simp
      show "(0::real) < 2" by simp
      show "(2::real) \<le> 2 + tau"
        using tau_lower by linarith
    qed
    then show ?thesis by simp
  qed
  have natural_ratio_at_least_one:
      "1 \<le> ln (2 + tau) / ln 2"
    using log_growth_at_least_one by (simp add: log_def)
  have static_growth:
      "?C0 \<le> ln (2 + tau) * (?C0 / ln 2)"
  proof -
    have weighted:
        "?C0 * 1 \<le> ?C0 * (ln (2 + tau) / ln 2)"
      by (rule mult_left_mono[OF natural_ratio_at_least_one
            C0_nonnegative])
    show ?thesis
      using weighted by (simp add: divide_inverse algebra_simps)
  qed
  have logarithmic_growth:
      "?C1 * (1 + log 2 (R * sqrt tau)) \<le>
        ln (2 + tau) *
          (?C1 * ((2 + log 2 R) / ln 2))"
  proof -
    have weighted:
        "?C1 * (1 + log 2 (R * sqrt tau)) \<le>
          ?C1 * (((2 + log 2 R) / ln 2) * ln (2 + tau))"
      by (rule mult_left_mono[OF logarithmic C1_nonnegative])
    show ?thesis
      using weighted by (simp add: algebra_simps)
  qed
  have bracket_bound:
      "?C0 + ?C1 * (1 + log 2 (R * sqrt tau)) \<le>
        ln (2 + tau) *
          (?C0 / ln 2 + ?C1 * ((2 + log 2 R) / ln 2))"
  proof -
    note combined = add_mono[OF static_growth logarithmic_growth]
    show ?thesis
      using combined by (simp add: algebra_simps)
  qed
  have outer_bound:
      "inverse (sqrt tau) *
          (?C0 + ?C1 * (1 + log 2 (R * sqrt tau))) \<le>
        inverse (sqrt tau) * ln (2 + tau) *
          (?C0 / ln 2 + ?C1 * ((2 + log 2 R) / ln 2))"
  proof -
    have scaled:
        "inverse (sqrt tau) *
            (?C0 + ?C1 * (1 + log 2 (R * sqrt tau))) \<le>
          inverse (sqrt tau) *
            (ln (2 + tau) *
              (?C0 / ln 2 + ?C1 * ((2 + log 2 R) / ln 2)))"
      by (rule mult_left_mono[OF bracket_bound])
         (simp add: tau_nonnegative)
    show ?thesis
      using scaled by (simp add: algebra_simps)
  qed
  show natural_log_bound:
      "(let
          P = Real_Vector_Spaces.norm
            (inverse (of_real pi :: complex));
          K = P *
            (integral\<^sup>L lborel
              (\<lambda>x. abs (slp_localized_cauchy_kernel (2 * A) x)
                powr q)) powr (1 / q);
          W = slp_w1p_norm_on b X u Du;
          M = K * (192 * W);
          I = integral\<^sup>L lborel (slp_localized_cauchy_kernel 1);
          J = integral\<^sup>L lborel (slp_squared_radial_annulus 1 2);
          C = 6 * I + 2 * unit_ball_vol 2;
          N0 = P * M * C;
          B0 = 2 * M;
          DB0 = K * (2 * (4 * W));
          CB0 = ((P * slp_global_cutoff_L) * M) * C;
          C0 = N0 + (B0 + (DB0 + (CB0 + P * M * I)));
          C1 = P * M * J
        in
          AE z in lborel. z \<in> X \<longrightarrow>
            Real_Vector_Spaces.norm
              (slp_partial_psi_inverse tau c
                (slp_restrict_field X u) z) \<le>
            inverse (sqrt tau) * ln (2 + tau) *
              (C0 / ln 2 + C1 * ((2 + log 2 R) / ln 2)))"
    unfolding Let_def
  proof (use regrouped_bound in eventually_elim)
    fix z :: slp_point
    assume pointwise:
      "z \<in> X \<longrightarrow>
        Real_Vector_Spaces.norm
          (slp_partial_psi_inverse tau c
            (slp_restrict_field X u) z) \<le>
        inverse (sqrt tau) *
          (?C0 + ?C1 * (1 + log 2 (R * sqrt tau)))"
    show "z \<in> X \<longrightarrow>
        Real_Vector_Spaces.norm
          (slp_partial_psi_inverse tau c
            (slp_restrict_field X u) z) \<le>
        inverse (sqrt tau) * ln (2 + tau) *
          (?C0 / ln 2 + ?C1 * ((2 + log 2 R) / ln 2))"
    proof
      assume z_in: "z \<in> X"
      have "Real_Vector_Spaces.norm
          (slp_partial_psi_inverse tau c
            (slp_restrict_field X u) z) \<le>
          inverse (sqrt tau) *
            (?C0 + ?C1 * (1 + log 2 (R * sqrt tau)))"
        by (rule pointwise[THEN mp, OF z_in])
      also have "... \<le>
          inverse (sqrt tau) * ln (2 + tau) *
            (?C0 / ln 2 + ?C1 * ((2 + log 2 R) / ln 2))"
        by (rule outer_bound)
      finally show "Real_Vector_Spaces.norm
          (slp_partial_psi_inverse tau c
            (slp_restrict_field X u) z) \<le>
        inverse (sqrt tau) * ln (2 + tau) *
          (?C0 / ln 2 + ?C1 * ((2 + log 2 R) / ln 2))" .
    qed
  qed
qed

end

end
