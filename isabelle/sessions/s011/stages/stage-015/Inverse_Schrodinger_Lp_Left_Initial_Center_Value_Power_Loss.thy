theory Inverse_Schrodinger_Lp_Left_Initial_Center_Value_Power_Loss
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_015.Inverse_Schrodinger_Lp_W1p_Rough_Zero_Extended_Esssup_Natural_Log_Bound"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_015.Inverse_Schrodinger_Lp_Nested_Coefficient_Product_Power_Loss_Esssup"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_014.Inverse_Schrodinger_Lp_W1p_Zero_Smooth_Multiplier"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Initial center-value power-loss bound\<close>

context slp_cauchy_local_w1s
begin

theorem slp_left_initial_center_value_esssup_power_loss_bound:
  fixes p epsilon A R :: real
    and X :: "slp_point set"
    and cutoff :: slp_scalar_field
  assumes riesz_hls: "aim_planar_riesz_hls_claim"
    and cauchy_test_left_inverse:
      "aim_planar_cauchy_test_left_inverse_claim"
    and exponent_lower: "1 < p"
    and exponent_upper: "p < 2"
    and loss_positive: "0 < epsilon"
    and radius_nonnegative: "0 \<le> A"
    and radius_lower: "1 \<le> R"
    and set_radius:
      "\<And>y :: slp_point. y \<in> X \<Longrightarrow>
        Real_Vector_Spaces.norm y \<le> A"
    and X_open: "open X"
    and X_bounded: "bounded X"
    and cutoff_test: "slp_test_function_on X cutoff"
  shows
    "\<exists>C::real. 0 < C \<and>
      (\<forall>tau c center_value.
        2 \<le> tau \<and>
        (\<forall>y. y \<in> X \<longrightarrow>
          Real_Vector_Spaces.norm (y - c) \<le> R)
        \<longrightarrow>
        (\<lambda>z :: slp_point.
          ereal (Real_Vector_Spaces.norm
            (slp_restrict_field X
              (slp_partial_psi_inverse tau c
                (\<lambda>x. cutoff x * center_value)) z)))
          \<in> borel_measurable (lborel :: slp_point measure)
        \<and>
        esssup (lborel :: slp_point measure)
          (\<lambda>z :: slp_point.
            ereal (Real_Vector_Spaces.norm
              (slp_restrict_field X
                (slp_partial_psi_inverse tau c
                  (\<lambda>x. cutoff x * center_value)) z)))
          \<le> ereal
            (C * tau powr (-(1 - 1 / p) + epsilon) *
              Real_Vector_Spaces.norm center_value))"
proof -
  have X_measurable: "X \<in> sets lborel"
    using X_open by simp
  have outer_context: "slp_qstar_centered_smooth_far_hls_context"
    using aim_planar_hls_cauchy riesz_hls cauchy_test_left_inverse
    by unfold_locales
  have cutoff_zero:
      "slp_w1p_zero_pair_on 3 X cutoff (slp_classical_gradient cutoff)"
    by (rule slp_test_function_w1p_zero_pair[OF _ cutoff_test]) simp
  have cutoff_pair:
      "slp_w1p_pair_on 3 X cutoff (slp_classical_gradient cutoff)"
    using cutoff_zero unfolding slp_w1p_zero_pair_on_def by blast
  have cutoff_support: "closure {x. cutoff x \<noteq> 0} \<subseteq> X"
    using cutoff_test unfolding slp_test_function_on_def by blast
  have restrict_cutoff_product:
      "slp_restrict_field X (\<lambda>x. h x * cutoff x) =
        (\<lambda>x. h x * cutoff x)" for h :: slp_scalar_field
  proof (rule ext)
    fix x
    show "slp_restrict_field X (\<lambda>x. h x * cutoff x) x =
        h x * cutoff x"
    proof (cases "x \<in> X")
      case True
      then show ?thesis by (simp add: slp_restrict_field_def)
    next
      case False
      have cutoff_zero_at: "cutoff x = 0"
      proof (rule ccontr)
        assume "cutoff x \<noteq> 0"
        then have "x \<in> closure {x. cutoff x \<noteq> 0}"
          unfolding closure_def by simp
        with cutoff_support False show False by blast
      qed
      show ?thesis using False cutoff_zero_at
        by (simp add: slp_restrict_field_def)
    qed
  qed

  let ?q = "slp_holder_conjugate 3"
  let ?P =
    "Real_Vector_Spaces.norm (inverse (of_real pi :: complex))"
  let ?L =
    "?P *
      (integral\<^sup>L lborel
        (\<lambda>x. abs (slp_localized_cauchy_kernel (2 * A) x) powr ?q))
        powr (1 / ?q)"
  let ?I = "integral\<^sup>L lborel (slp_localized_cauchy_kernel 1)"
  let ?J = "integral\<^sup>L lborel (slp_squared_radial_annulus 1 2)"
  let ?H = "6 * ?I + 2 * unit_ball_vol 2"
  let ?RawFactor =
    "(?P * (?L * 192) * ?H +
      (2 * (?L * 192) +
        (?L * 8 +
          (((?P * slp_global_cutoff_L) * (?L * 192)) * ?H +
            ?P * (?L * 192) * ?I)))) / ln 2 +
      (?P * (?L * 192) * ?J) * ((2 + log 2 R) / ln 2)"
  let ?SafeFactor = "abs ?RawFactor + 1"
  let ?W0 =
    "slp_w1p_norm_on 3 X cutoff (slp_classical_gradient cutoff)"
  let ?Scale = "36 * ?W0"
  let ?eta = "1 / p - 1 / 2 + epsilon"

  have target_positive: "0 < aim_hls_target_exponent p"
    using slp_qstar_exponent_relations(1)[OF exponent_lower exponent_upper]
    by linarith
  have target_reciprocal_positive:
      "0 < 1 / aim_hls_target_exponent p"
    using target_positive by simp
  have reciprocal_gap_positive: "0 < 1 / p - 1 / 2"
    using target_reciprocal_positive
    by (simp only: slp_hls_target_exponent_reciprocal[
          OF exponent_lower exponent_upper])
  have eta_positive: "0 < ?eta"
    using reciprocal_gap_positive loss_positive by linarith
  obtain K :: real where K_positive: "0 < K"
    and absorption:
      "\<forall>tau. 2 \<le> tau \<longrightarrow>
        (inverse (sqrt tau) * ln (2 + tau)) powr 1
          \<le> K * tau powr (- 1 / 2 + ?eta)"
    using slp_logarithmic_interpolation_power_absorption[
      of 1 ?eta, OF zero_less_one eta_positive] by blast
  have exponent_identity:
      "- 1 / 2 + ?eta = -(1 - 1 / p) + epsilon"
    by (simp add: algebra_simps)
  have safe_positive: "0 < ?SafeFactor"
    by simp
  have safe_nonnegative: "0 \<le> ?SafeFactor"
    using safe_positive by linarith
  have W0_nonnegative: "0 \<le> ?W0"
    unfolding slp_w1p_norm_on_def by simp
  have scale_nonnegative: "0 \<le> ?Scale"
    using W0_nonnegative by simp
  let ?BaseC = "?SafeFactor * ?Scale * K"
  let ?FinalC = "?BaseC + 1"
  have baseC_nonnegative: "0 \<le> ?BaseC"
    by (rule mult_nonneg_nonneg[OF
          mult_nonneg_nonneg[OF safe_nonnegative scale_nonnegative]
          less_imp_le[OF K_positive]])
  have C_positive: "0 < ?FinalC"
    using baseC_nonnegative by linarith

  show ?thesis
  proof (rule exI[of _ ?FinalC], rule conjI[OF C_positive])
    show "\<forall>tau c center_value.
        2 \<le> tau \<and>
        (\<forall>y. y \<in> X \<longrightarrow>
          Real_Vector_Spaces.norm (y - c) \<le> R)
        \<longrightarrow>
        (\<lambda>z :: slp_point.
          ereal (Real_Vector_Spaces.norm
            (slp_restrict_field X
              (slp_partial_psi_inverse tau c
                (\<lambda>x. cutoff x * center_value)) z)))
          \<in> borel_measurable (lborel :: slp_point measure)
        \<and>
        esssup (lborel :: slp_point measure)
          (\<lambda>z :: slp_point.
            ereal (Real_Vector_Spaces.norm
              (slp_restrict_field X
                (slp_partial_psi_inverse tau c
                  (\<lambda>x. cutoff x * center_value)) z)))
          \<le> ereal
            (?FinalC * tau powr (-(1 - 1 / p) + epsilon) *
              Real_Vector_Spaces.norm center_value)"
    proof (intro allI impI)
      fix tau :: real and c :: slp_point and center_value :: complex
      assume data:
        "2 \<le> tau \<and>
          (\<forall>y. y \<in> X \<longrightarrow>
            Real_Vector_Spaces.norm (y - c) \<le> R)"
      have tau_lower: "2 \<le> tau" using data by blast
      have relative_radius:
          "\<And>y :: slp_point. y \<in> X \<Longrightarrow>
            Real_Vector_Spaces.norm (y - c) \<le> R"
        using data by blast
      let ?a = "\<lambda>_ :: slp_point. center_value"
      let ?u = "\<lambda>x. ?a x * cutoff x"
      let ?Du = "\<lambda>x. \<chi> i.
        ?a x * slp_classical_gradient cutoff x $ i +
          cutoff x * slp_complex_partial_derivative ?a i x"
      let ?W = "slp_w1p_norm_on 3 X ?u ?Du"
      let ?M0 = "?L * (192 * ?W)"
      let ?N0 = "?P * ?M0 * ?H"
      let ?B0 = "2 * ?M0"
      let ?DB0 = "?L * (2 * (4 * ?W))"
      let ?CB0 = "((?P * slp_global_cutoff_L) * ?M0) * ?H"
      let ?C0 = "?N0 + (?B0 + (?DB0 + (?CB0 + ?P * ?M0 * ?I)))"
      let ?C1 = "?P * ?M0 * ?J"
      let ?rate = "inverse (sqrt tau) * ln (2 + tau)"
      have a_smooth: "smooth_on UNIV ?a"
        by (rule smooth_on_const)
      have a_value_bound:
          "\<And>x. x \<in> X \<Longrightarrow>
            Real_Vector_Spaces.norm (?a x) \<le>
              Real_Vector_Spaces.norm center_value"
        by simp
      have a_derivative_zero:
          "\<And>x. x \<in> X \<Longrightarrow>
            Real_Vector_Spaces.norm
              (slp_complex_partial_derivative ?a 0 x) \<le> 0"
        by (simp add: slp_complex_partial_derivative_def)
      have a_derivative_one:
          "\<And>x. x \<in> X \<Longrightarrow>
            Real_Vector_Spaces.norm
              (slp_complex_partial_derivative ?a 1 x) \<le> 0"
        by (simp add: slp_complex_partial_derivative_def)
      have a_norm_nonnegative:
          "0 \<le> Real_Vector_Spaces.norm center_value"
        by simp
      have three_one: "1 \<le> (3::real)"
        by simp
      have three_above_two: "(2::real) < 3"
        by simp
      have zero_real: "0 \<le> (0::real)"
        by simp
      have zero_pair: "slp_w1p_zero_pair_on 3 X ?u ?Du"
        by (rule slp_w1p_zero_pair_on_mult_smooth_bounded[
              OF three_one X_measurable X_bounded cutoff_zero a_smooth
                a_value_bound a_derivative_zero a_derivative_one
                a_norm_nonnegative zero_real zero_real])
      have W_bound:
          "?W \<le> ?Scale * Real_Vector_Spaces.norm center_value"
        using slp_w1p_norm_on_mult_smooth_bounded[
          OF three_one X_measurable X_bounded cutoff_pair a_smooth
            a_value_bound a_derivative_zero a_derivative_one
            a_norm_nonnegative zero_real zero_real]
        by (simp add: algebra_simps)
      have restrict_u: "slp_restrict_field X ?u = ?u"
        by (rule restrict_cutoff_product)
      note rough =
        slp_qstar_centered_smooth_far_hls_context.slp_w1p_zero_pair_partial_psi_inverse_rough_zero_extended_esssup_natural_log_bound[
          OF outer_context tau_lower three_above_two radius_nonnegative radius_lower
            set_radius relative_radius X_measurable zero_pair]
      have output_measurable:
          "(\<lambda>z :: slp_point.
            ereal (Real_Vector_Spaces.norm
              (slp_restrict_field X
                (slp_partial_psi_inverse tau c ?u) z)))
            \<in> borel_measurable (lborel :: slp_point measure)"
        using rough(1) by (simp only: restrict_u)
      have rough_bound:
          "esssup (lborel :: slp_point measure)
              (\<lambda>z :: slp_point.
                ereal (Real_Vector_Spaces.norm
                  (slp_restrict_field X
                    (slp_partial_psi_inverse tau c ?u) z)))
            \<le> ereal
              (?rate *
                (?C0 / ln 2 + ?C1 * ((2 + log 2 R) / ln 2)))"
        using rough(2)
        unfolding Let_def
        by (simp only: restrict_u)
      have bracket_factor:
          "?C0 / ln 2 + ?C1 * ((2 + log 2 R) / ln 2) =
            ?RawFactor * ?W"
        by (simp add: algebra_simps)
      have W_nonnegative: "0 \<le> ?W"
        unfolding slp_w1p_norm_on_def by simp
      have raw_le_safe: "?RawFactor \<le> ?SafeFactor"
      proof (rule order_trans[OF abs_ge_self])
        show "abs ?RawFactor \<le> ?SafeFactor" by simp
      qed
      have bracket_le:
          "?C0 / ln 2 + ?C1 * ((2 + log 2 R) / ln 2) \<le>
            ?SafeFactor * ?W"
        using mult_right_mono[OF raw_le_safe W_nonnegative]
        by (simp only: bracket_factor)
      have tau_nonnegative: "0 \<le> tau"
        using tau_lower by linarith
      have inverse_sqrt_nonnegative: "0 \<le> inverse (sqrt tau)"
        by (simp add: tau_nonnegative)
      have ln_parameter_nonnegative: "0 \<le> ln (2 + tau)"
      proof (rule less_imp_le, rule ln_gt_zero)
        show "(1::real) < 2 + tau"
          using tau_lower by linarith
      qed
      have rate_nonnegative: "0 \<le> ?rate"
        by (rule mult_nonneg_nonneg[OF inverse_sqrt_nonnegative
              ln_parameter_nonnegative])
      have bracket_scaled:
          "?rate *
              (?C0 / ln 2 + ?C1 * ((2 + log 2 R) / ln 2))
            \<le> ?rate * (?SafeFactor * ?W)"
        by (rule mult_left_mono[OF bracket_le rate_nonnegative])
      have W_scaled:
          "?rate * (?SafeFactor * ?W) \<le>
            ?rate *
              (?SafeFactor *
                (?Scale * Real_Vector_Spaces.norm center_value))"
      proof (rule mult_left_mono[OF _ rate_nonnegative])
        show "?SafeFactor * ?W \<le>
            ?SafeFactor *
              (?Scale * Real_Vector_Spaces.norm center_value)"
          by (rule mult_left_mono[OF W_bound safe_nonnegative])
      qed
      have rate_bound:
          "?rate \<le>
            K * tau powr (-(1 - 1 / p) + epsilon)"
      proof -
        have "?rate = ?rate powr 1"
          by (rule sym, rule powr_one[OF rate_nonnegative])
        also have "... \<le> K * tau powr (- 1 / 2 + ?eta)"
          by (rule absorption[rule_format, OF tau_lower])
        also have "... =
            K * tau powr (-(1 - 1 / p) + epsilon)"
          by (simp only: exponent_identity)
        finally show ?thesis .
      qed
      have amplitude_nonnegative:
          "0 \<le> ?SafeFactor *
            (?Scale * Real_Vector_Spaces.norm center_value)"
        using safe_nonnegative scale_nonnegative
        by (intro mult_nonneg_nonneg) simp_all
      have rate_scaled:
          "?rate *
              (?SafeFactor *
                (?Scale * Real_Vector_Spaces.norm center_value))
            \<le>
            (K * tau powr (-(1 - 1 / p) + epsilon)) *
              (?SafeFactor *
                (?Scale * Real_Vector_Spaces.norm center_value))"
        by (rule mult_right_mono[OF rate_bound amplitude_nonnegative])
      have target_power_nonnegative:
          "0 \<le> tau powr (-(1 - 1 / p) + epsilon)"
        by (rule powr_ge_zero)
      have target_factor_nonnegative:
          "0 \<le> tau powr (-(1 - 1 / p) + epsilon) *
            Real_Vector_Spaces.norm center_value"
        by (rule mult_nonneg_nonneg[OF target_power_nonnegative]) simp
      have baseC_le_C: "?BaseC \<le> ?FinalC"
        by simp
      have coefficient_enlarged:
          "?BaseC *
              (tau powr (-(1 - 1 / p) + epsilon) *
                Real_Vector_Spaces.norm center_value)
            \<le>
            ?FinalC *
              (tau powr (-(1 - 1 / p) + epsilon) *
                Real_Vector_Spaces.norm center_value)"
        by (rule mult_right_mono[OF baseC_le_C
              target_factor_nonnegative])
      have real_bound:
          "?rate *
              (?C0 / ln 2 + ?C1 * ((2 + log 2 R) / ln 2))
            \<le>
            ?FinalC * tau powr (-(1 - 1 / p) + epsilon) *
              Real_Vector_Spaces.norm center_value"
      proof -
        have "?rate *
              (?C0 / ln 2 + ?C1 * ((2 + log 2 R) / ln 2))
            \<le> ?rate * (?SafeFactor * ?W)"
          by (rule bracket_scaled)
        also have "... \<le> ?rate *
              (?SafeFactor *
                (?Scale * Real_Vector_Spaces.norm center_value))"
          by (rule W_scaled)
        also have "... \<le>
            (K * tau powr (-(1 - 1 / p) + epsilon)) *
              (?SafeFactor *
                (?Scale * Real_Vector_Spaces.norm center_value))"
          by (rule rate_scaled)
        also have "... = ?BaseC *
              (tau powr (-(1 - 1 / p) + epsilon) *
                Real_Vector_Spaces.norm center_value)"
          by (simp add: algebra_simps)
        also have "... \<le> ?FinalC *
              (tau powr (-(1 - 1 / p) + epsilon) *
                Real_Vector_Spaces.norm center_value)"
          by (rule coefficient_enlarged)
        also have "... =
            ?FinalC * tau powr (-(1 - 1 / p) + epsilon) *
              Real_Vector_Spaces.norm center_value"
          by (simp only: mult.assoc)
        finally show ?thesis .
      qed
      have esssup_bound:
          "esssup (lborel :: slp_point measure)
              (\<lambda>z :: slp_point.
                ereal (Real_Vector_Spaces.norm
                  (slp_restrict_field X
                    (slp_partial_psi_inverse tau c ?u) z)))
            \<le> ereal
              (?FinalC * tau powr (-(1 - 1 / p) + epsilon) *
                Real_Vector_Spaces.norm center_value)"
        by (rule order_trans[OF rough_bound])
          (use real_bound in simp)
      show
          "(\<lambda>z :: slp_point.
            ereal (Real_Vector_Spaces.norm
              (slp_restrict_field X
                (slp_partial_psi_inverse tau c
                  (\<lambda>x. cutoff x * center_value)) z)))
            \<in> borel_measurable (lborel :: slp_point measure)
          \<and>
          esssup (lborel :: slp_point measure)
            (\<lambda>z :: slp_point.
              ereal (Real_Vector_Spaces.norm
                (slp_restrict_field X
                  (slp_partial_psi_inverse tau c
                    (\<lambda>x. cutoff x * center_value)) z)))
            \<le> ereal
              (?FinalC * tau powr (-(1 - 1 / p) + epsilon) *
                Real_Vector_Spaces.norm center_value)"
        using output_measurable esssup_bound
        by (simp add: mult.commute)
    qed
  qed
qed

end

end
