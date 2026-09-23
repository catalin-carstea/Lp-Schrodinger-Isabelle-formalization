theory Inverse_Schrodinger_Lp_W1p_Rough_Zero_Extended_Esssup_Natural_Log_Bound
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_015.Inverse_Schrodinger_Lp_W1p_Rough_Near_Far_AE_Natural_Log_Bound"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_011.Inverse_Schrodinger_Lp_Two_Cauchy_Test_Cutoff"
    "HOL-Probability.Essential_Supremum"
begin

section \<open>Zero-extended essential-supremum natural-logarithmic control\<close>

context slp_qstar_centered_smooth_far_hls_context
begin

theorem
  slp_w1p_zero_pair_partial_psi_inverse_rough_zero_extended_esssup_natural_log_bound:
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
  shows zero_extended_modulus_measurable:
      "(\<lambda>z :: slp_point.
        ereal (Real_Vector_Spaces.norm
          (slp_restrict_field X
            (slp_partial_psi_inverse tau c
              (slp_restrict_field X u)) z)))
        \<in> borel_measurable (lborel :: slp_point measure)"
    and zero_extended_esssup_bound:
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
          esssup (lborel :: slp_point measure)
            (\<lambda>z :: slp_point.
              ereal (Real_Vector_Spaces.norm
                (slp_restrict_field X
                  (slp_partial_psi_inverse tau c
                    (slp_restrict_field X u)) z)))
          \<le>
          ereal
            (inverse (sqrt tau) * ln (2 + tau) *
              (C0 / ln 2 + C1 * ((2 + log 2 R) / ln 2))))"
proof -
  let ?f = "slp_restrict_field X u"
  let ?g = "slp_oscillatory_modulation tau c ?f"
  let ?F = "slp_partial_psi_inverse tau c ?f"
  let ?h =
    "\<lambda>z :: slp_point.
      ereal (Real_Vector_Spaces.norm (slp_restrict_field X ?F z))"

  have X_bounded: "bounded X"
    unfolding bounded_iff
  proof (rule exI[of _ A], intro ballI)
    fix y :: slp_point
    assume y_in: "y \<in> X"
    show "Real_Vector_Spaces.norm y \<le> A"
      by (rule set_radius[OF y_in])
  qed
  have pair: "slp_w1p_pair_on b X u Du"
    using zero_pair unfolding slp_w1p_zero_pair_on_def by blast
  have restricted_lp: "aim_complex_lp_on_plane b ?f"
    using pair
    unfolding slp_w1p_pair_on_def slp_complex_lp_on_def by blast
  have modulated_lp: "aim_complex_lp_on_plane b ?g"
    using restricted_lp by simp
  have restricted_support_subset: "{y. ?f y \<noteq> 0} \<subseteq> X"
    unfolding slp_restrict_field_def by auto
  have restricted_support_bounded: "bounded {y. ?f y \<noteq> 0}"
    by (rule bounded_subset[OF X_bounded restricted_support_subset])
  have modulated_support_bounded: "bounded {y. ?g y \<noteq> 0}"
    using restricted_support_bounded by simp
  have transform_measurable:
      "slp_cauchy_transform SLP_Partial_Inverse ?g
        \<in> borel_measurable lborel"
    by (rule slp_cauchy_transform_measurable_above_two_bounded_support[
          OF exponent_above_two modulated_lp modulated_support_bounded])
  have output_measurable: "?F \<in> borel_measurable lborel"
    using transform_measurable
    unfolding slp_partial_psi_inverse_def by simp
  have restricted_output_measurable:
      "slp_restrict_field X ?F \<in> borel_measurable lborel"
    by (rule slp_restrict_field_measurable[
          OF X_measurable output_measurable])
  have h_measurable:
      "?h \<in> borel_measurable (lborel :: slp_point measure)"
    using restricted_output_measurable by measurable
  show zero_extended_modulus_measurable:
      "(\<lambda>z :: slp_point.
        ereal (Real_Vector_Spaces.norm
          (slp_restrict_field X
            (slp_partial_psi_inverse tau c
              (slp_restrict_field X u)) z)))
        \<in> borel_measurable (lborel :: slp_point measure)"
    by (rule h_measurable)

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
  let ?E =
    "inverse (sqrt tau) * ln (2 + tau) *
      (?C0 / ln 2 + ?C1 * ((2 + log 2 R) / ln 2))"

  note base =
    slp_w1p_zero_pair_partial_psi_inverse_rough_AE_natural_log_bound[
      where b=b and A=A and R=R and tau=tau and c=c and X=X
        and u=u and Du=Du,
      OF tau_lower exponent_above_two radius_nonnegative radius_lower
        set_radius relative_radius X_measurable zero_pair,
      folded q_def]
  have output_AE_bound:
      "AE z in lborel. z \<in> X \<longrightarrow>
        Real_Vector_Spaces.norm (?F z) \<le> ?E"
    using base(2) unfolding Let_def by blast

  have tau_nonnegative: "0 \<le> tau"
    using tau_lower by linarith
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

  have log_R_nonnegative: "0 \<le> log 2 R"
  proof -
    have "log 2 1 \<le> log 2 R"
    proof (rule log_mono)
      show "(1::real) < 2" by simp
      show "(0::real) < 1" by simp
      show "(1::real) \<le> R" by (rule radius_lower)
    qed
    then show ?thesis by simp
  qed
  have ln_two_positive: "0 < ln (2::real)"
    by simp
  have ln_parameter_nonnegative: "0 \<le> ln (2 + tau)"
  proof (rule less_imp_le, rule ln_gt_zero)
    show "(1::real) < 2 + tau"
      using tau_lower by linarith
  qed
  have inverse_sqrt_nonnegative: "0 \<le> inverse (sqrt tau)"
    by (simp add: tau_nonnegative)
  have C0_ratio_nonnegative: "0 \<le> ?C0 / ln 2"
    by (rule divide_nonneg_pos[OF C0_nonnegative ln_two_positive])
  have radius_numerator_nonnegative: "0 \<le> 2 + log 2 R"
    using log_R_nonnegative by linarith
  have radius_ratio_nonnegative:
      "0 \<le> (2 + log 2 R) / ln 2"
    by (rule divide_nonneg_pos[OF radius_numerator_nonnegative
          ln_two_positive])
  have C1_radius_nonnegative:
      "0 \<le> ?C1 * ((2 + log 2 R) / ln 2)"
    by (rule mult_nonneg_nonneg[OF C1_nonnegative
          radius_ratio_nonnegative])
  have bracket_nonnegative:
      "0 \<le> ?C0 / ln 2 + ?C1 * ((2 + log 2 R) / ln 2)"
    by (rule add_nonneg_nonneg[OF C0_ratio_nonnegative
          C1_radius_nonnegative])
  have rate_nonnegative:
      "0 \<le> inverse (sqrt tau) * ln (2 + tau)"
    by (rule mult_nonneg_nonneg[OF inverse_sqrt_nonnegative
          ln_parameter_nonnegative])
  have envelope_nonnegative: "0 \<le> ?E"
    by (rule mult_nonneg_nonneg[OF rate_nonnegative
          bracket_nonnegative])

  have zero_extended_AE_bound:
      "AE z in (lborel :: slp_point measure). ?h z \<le> ereal ?E"
    using output_AE_bound
  proof eventually_elim
    fix z :: slp_point
    assume pointwise:
      "z \<in> X \<longrightarrow> Real_Vector_Spaces.norm (?F z) \<le> ?E"
    show "?h z \<le> ereal ?E"
    proof (cases "z \<in> X")
      case True
      have "Real_Vector_Spaces.norm (?F z) \<le> ?E"
        by (rule pointwise[THEN mp, OF True])
      then show ?thesis
        by (simp add: slp_restrict_field_def True)
    next
      case False
      show ?thesis
        using envelope_nonnegative
        by (simp add: slp_restrict_field_def False)
    qed
  qed
  show zero_extended_esssup_bound:
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
          esssup (lborel :: slp_point measure)
            (\<lambda>z :: slp_point.
              ereal (Real_Vector_Spaces.norm
                (slp_restrict_field X
                  (slp_partial_psi_inverse tau c
                    (slp_restrict_field X u)) z)))
          \<le>
          ereal
            (inverse (sqrt tau) * ln (2 + tau) *
              (C0 / ln 2 + C1 * ((2 + log 2 R) / ln 2))))"
    unfolding Let_def
    by (rule esssup_I[OF h_measurable zero_extended_AE_bound])
qed

end

end
