theory Inverse_Schrodinger_Lp_W1p_Rough_Center_Natural_Log_Bound
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_014.Inverse_Schrodinger_Lp_W1p_Rough_Center_Inverse_Sqrt_Bound"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Natural_Logarithmic_Parameter_Comparison"
begin

section \<open>Natural-logarithmic bound at the phase center\<close>

context slp_qstar_centered_smooth_far_hls_context
begin

theorem slp_w1p_zero_pair_partial_psi_inverse_rough_center_natural_log_bound:
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
    and natural_log_bound:
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
          I = integral\<^sup>L lborel (slp_localized_cauchy_kernel 1);
          J = integral\<^sup>L lborel (slp_squared_radial_annulus 1 2);
          N0 = P * M * (6 * I + 2 * unit_ball_vol 2);
          DB0 = K * (2 * (4 * W));
          CB0 = (2 * slp_global_cutoff_L) *
            (K1 * pi powr (1 / b) * M);
          C0 = N0 + (DB0 + (CB0 + P * M * I));
          C1 = P * M * J
        in
          Real_Vector_Spaces.norm (slp_partial_psi_inverse tau c
            (slp_restrict_field X u) c) \<le>
            inverse (sqrt tau) * ln (2 + tau) *
              (C0 / ln 2 + C1 * ((2 + log 2 R) / ln 2)))"
proof -
  have tau_nonnegative: "0 \<le> tau"
    using tau_lower by linarith
  note base =
    slp_w1p_zero_pair_partial_psi_inverse_rough_center_inverse_sqrt_bound[
      where b=b and A=A and R=R and tau=tau and c=c and X=X
        and u=u and Du=Du,
      OF tau_lower exponent_above_two radius_nonnegative radius_lower
        set_radius relative_radius center_in X_measurable X_bounded
        zero_pair,
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
  let ?C0 = "?N0 + (?DB0 + (?CB0 + ?P * ?M * ?I))"
  let ?C1 = "?P * ?M * ?J"

  have raw_bound:
      "Real_Vector_Spaces.norm (slp_partial_psi_inverse tau c
          (slp_restrict_field X u) c) \<le>
        inverse (sqrt tau) *
          (?N0 +
            (?DB0 +
              (?CB0 +
                ?P * ?M *
                  (?I + (1 + log 2 (R * sqrt tau)) * ?J))))"
    using base(2)
    unfolding Let_def by blast
  have regroup:
      "?N0 +
          (?DB0 +
            (?CB0 +
              ?P * ?M *
                (?I + (1 + log 2 (R * sqrt tau)) * ?J))) =
        ?C0 + ?C1 * (1 + log 2 (R * sqrt tau))"
    by (simp add: algebra_simps)
  have center_bound:
      "Real_Vector_Spaces.norm (slp_partial_psi_inverse tau c
          (slp_restrict_field X u) c) \<le>
        inverse (sqrt tau) *
          (?C0 + ?C1 * (1 + log 2 (R * sqrt tau)))"
    using raw_bound by (simp only: regroup)

  have P_nonnegative: "0 \<le> ?P"
    by simp
  have K_nonnegative: "0 \<le> ?K"
    by (rule mult_nonneg_nonneg[OF P_nonnegative]) simp
  have K1_nonnegative: "0 \<le> ?K1"
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
  have cutoff_nonnegative: "0 \<le> slp_global_cutoff_L"
    using slp_global_cutoff_profile_spec[THEN conjunct2, THEN conjunct2,
        THEN conjunct1] .
  have PM_nonnegative: "0 \<le> ?P * ?M"
    by (rule mult_nonneg_nonneg[OF P_nonnegative M_nonnegative])
  have N_inner_nonnegative:
      "0 \<le> 6 * ?I + 2 * unit_ball_vol 2"
    using I_nonnegative by simp
  have N0_nonnegative: "0 \<le> ?N0"
    by (rule mult_nonneg_nonneg[OF PM_nonnegative
          N_inner_nonnegative])
  have DB0_nonnegative: "0 \<le> ?DB0"
    by (rule mult_nonneg_nonneg[OF K_nonnegative])
       (simp add: W_nonnegative)
  have cutoff_factor_nonnegative:
      "0 \<le> 2 * slp_global_cutoff_L"
    using cutoff_nonnegative by simp
  have pi_power_nonnegative: "0 \<le> pi powr (1 / b)"
    by simp
  have K1_pi_nonnegative: "0 \<le> ?K1 * pi powr (1 / b)"
    by (rule mult_nonneg_nonneg[OF K1_nonnegative
          pi_power_nonnegative])
  have K1_pi_M_nonnegative:
      "0 \<le> ?K1 * pi powr (1 / b) * ?M"
    by (rule mult_nonneg_nonneg[OF K1_pi_nonnegative M_nonnegative])
  have CB0_nonnegative: "0 \<le> ?CB0"
    by (rule mult_nonneg_nonneg[OF cutoff_factor_nonnegative
          K1_pi_M_nonnegative])
  have PMI_nonnegative: "0 \<le> ?P * ?M * ?I"
    by (rule mult_nonneg_nonneg[OF PM_nonnegative I_nonnegative])
  have C0_tail_nonnegative: "0 \<le> ?CB0 + ?P * ?M * ?I"
    by (rule add_nonneg_nonneg[OF CB0_nonnegative PMI_nonnegative])
  have C0_middle_nonnegative:
      "0 \<le> ?DB0 + (?CB0 + ?P * ?M * ?I)"
    by (rule add_nonneg_nonneg[OF DB0_nonnegative
          C0_tail_nonnegative])
  have C0_nonnegative: "0 \<le> ?C0"
    by (rule add_nonneg_nonneg[OF N0_nonnegative
          C0_middle_nonnegative])
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
          I = integral\<^sup>L lborel (slp_localized_cauchy_kernel 1);
          J = integral\<^sup>L lborel (slp_squared_radial_annulus 1 2);
          N0 = P * M * (6 * I + 2 * unit_ball_vol 2);
          DB0 = K * (2 * (4 * W));
          CB0 = (2 * slp_global_cutoff_L) *
            (K1 * pi powr (1 / b) * M);
          C0 = N0 + (DB0 + (CB0 + P * M * I));
          C1 = P * M * J
        in
          Real_Vector_Spaces.norm (slp_partial_psi_inverse tau c
            (slp_restrict_field X u) c) \<le>
            inverse (sqrt tau) * ln (2 + tau) *
              (C0 / ln 2 + C1 * ((2 + log 2 R) / ln 2)))"
    unfolding Let_def
    by (rule order_trans[OF center_bound outer_bound])
qed

end

end
