theory Inverse_Schrodinger_Lp_Nested_Coefficient_Product_Right_High_Esssup
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_016.Inverse_Schrodinger_Lp_Right_W1p_Rough_Zero_Extended_Esssup_Natural_Log_Bound"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_015.Inverse_Schrodinger_Lp_Inner_Cauchy_Coefficient_Product_Cutoff_Norm"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Actual decaying above-two right coefficient endpoint\<close>

context slp_cauchy_local_w1s
begin

theorem slp_nested_coefficient_product_right_high_esssup_bound:
  fixes b A R A0 B0 B1 :: real
    and X Y :: "slp_point set"
    and cutoff :: slp_scalar_field
  assumes riesz_hls: "aim_planar_riesz_hls_claim"
    and cauchy_test_left_inverse:
      "aim_planar_cauchy_test_left_inverse_claim"
    and evans_density: "evans_compact_support_w1p_zero_density_claim"
    and exponent_above_two: "2 < b"
    and radius_nonnegative: "0 \<le> A"
    and radius_lower: "1 \<le> R"
    and set_radius:
      "\<And>y :: slp_point. y \<in> X \<Longrightarrow>
        Real_Vector_Spaces.norm y \<le> A"
    and X_open: "open X"
    and X_bounded: "bounded X"
    and Y_bounded: "bounded Y"
    and cutoff_test: "slp_test_function_on X cutoff"
    and cutoff_bound:
      "\<And>x. x \<in> X \<Longrightarrow>
        Real_Vector_Spaces.norm (cutoff x) \<le> A0"
    and cutoff_derivative_zero_bound:
      "\<And>x. x \<in> X \<Longrightarrow>
        Real_Vector_Spaces.norm
          (slp_complex_partial_derivative cutoff 0 x) \<le> B0"
    and cutoff_derivative_one_bound:
      "\<And>x. x \<in> X \<Longrightarrow>
        Real_Vector_Spaces.norm
          (slp_complex_partial_derivative cutoff 1 x) \<le> B1"
    and A0_nonnegative: "0 \<le> A0"
    and B0_nonnegative: "0 \<le> B0"
    and B1_nonnegative: "0 \<le> B1"
  shows
    "\<exists>C::real. 0 < C \<and>
      (\<forall>tau c coefficient multiplier M.
        2 \<le> tau \<and>
        (\<forall>y. y \<in> X \<longrightarrow>
          Real_Vector_Spaces.norm (y - c) \<le> R) \<and>
        aim_complex_lp_on_plane b coefficient \<and>
        {x. coefficient x \<noteq> 0} \<subseteq> Y \<and>
        multiplier \<in> borel_measurable lborel \<and>
        (AE x in lborel. norm (multiplier x) \<le> M) \<and>
        0 \<le> M
        \<longrightarrow>
        (\<lambda>z :: slp_point.
          ereal (Real_Vector_Spaces.norm
            (slp_restrict_field X
              (slp_dbar_psi_inverse (- tau) c
                (\<lambda>x. cutoff x *
                  slp_partial_psi_inverse (- tau) c
                    (\<lambda>y. coefficient y * multiplier y) x)) z)))
          \<in> borel_measurable (lborel :: slp_point measure)
        \<and>
        esssup (lborel :: slp_point measure)
          (\<lambda>z :: slp_point.
            ereal (Real_Vector_Spaces.norm
              (slp_restrict_field X
                (slp_dbar_psi_inverse (- tau) c
                  (\<lambda>x. cutoff x *
                    slp_partial_psi_inverse (- tau) c
                      (\<lambda>y. coefficient y * multiplier y) x)) z)))
          \<le> ereal
            (C * inverse (sqrt tau) * ln (2 + tau) * M *
              aim_complex_lp_norm b coefficient))"
proof -
  have exponent_lower: "1 < b"
    using exponent_above_two by linarith
  have exponent_positive: "0 < b"
    using exponent_above_two by linarith
  have X_measurable: "X \<in> sets lborel"
    using X_open by simp
  obtain K :: real where K_positive: "0 < K"
    and inner_gain:
      "\<And>tau c coefficient multiplier M.
        aim_complex_lp_on_plane b coefficient \<Longrightarrow>
        {x. coefficient x \<noteq> 0} \<subseteq> Y \<Longrightarrow>
        multiplier \<in> borel_measurable lborel \<Longrightarrow>
        (AE x in lborel. norm (multiplier x) \<le> M) \<Longrightarrow>
        0 \<le> M \<Longrightarrow>
        slp_w1p_norm_on b X
            (\<lambda>x. cutoff x *
              slp_dbar_psi_inverse tau c
                (\<lambda>y. coefficient y * multiplier y) x)
            (\<lambda>x. \<chi> i.
              cutoff x *
                slp_dbar_inverse_gradient
                  (slp_oscillatory_modulation (- tau) c
                    (\<lambda>y. coefficient y * multiplier y)) x $ i +
              slp_dbar_psi_inverse tau c
                  (\<lambda>y. coefficient y * multiplier y) x *
                slp_complex_partial_derivative cutoff i x)
          \<le> K * M * aim_complex_lp_norm b coefficient
        \<and>
        slp_w1p_norm_on b X
            (\<lambda>x. cutoff x *
              slp_partial_psi_inverse (- tau) c
                (\<lambda>y. coefficient y * multiplier y) x)
            (\<lambda>x. \<chi> i.
              cutoff x *
                slp_partial_inverse_gradient
                  (slp_oscillatory_modulation (- tau) c
                    (\<lambda>y. coefficient y * multiplier y)) x $ i +
              slp_partial_psi_inverse (- tau) c
                  (\<lambda>y. coefficient y * multiplier y) x *
                slp_complex_partial_derivative cutoff i x)
          \<le> K * M * aim_complex_lp_norm b coefficient"
    using slp_both_inner_cauchy_coefficient_product_cutoff_w1p_norm_bounds[
      OF exponent_lower X_open X_bounded Y_bounded cutoff_test cutoff_bound
        cutoff_derivative_zero_bound cutoff_derivative_one_bound
        A0_nonnegative B0_nonnegative B1_nonnegative]
    by blast
  have outer_context: "slp_qstar_centered_smooth_far_hls_context"
    using aim_planar_hls_cauchy riesz_hls cauchy_test_left_inverse
    by unfold_locales
  let ?q = "slp_holder_conjugate b"
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
  let ?C = "?SafeFactor * K"
  have G_positive: "0 < ?SafeFactor"
    by simp
  have G_nonnegative: "0 \<le> ?SafeFactor"
    using G_positive by linarith
  have C_positive: "0 < ?C"
    by (rule mult_pos_pos[OF G_positive K_positive])
  have cutoff_support: "closure {x. cutoff x \<noteq> 0} \<subseteq> X"
    using cutoff_test unfolding slp_test_function_on_def by blast
  have restrict_cutoff_product:
      "slp_restrict_field X (\<lambda>x. cutoff x * h x) =
        (\<lambda>x. cutoff x * h x)" for h :: slp_scalar_field
  proof (rule ext)
    fix x
    show "slp_restrict_field X (\<lambda>x. cutoff x * h x) x =
        cutoff x * h x"
    proof (cases "x \<in> X")
      case True
      then show ?thesis by (simp add: slp_restrict_field_def)
    next
      case False
      have cutoff_zero: "cutoff x = 0"
      proof (rule ccontr)
        assume "cutoff x \<noteq> 0"
        then have "x \<in> closure {x. cutoff x \<noteq> 0}"
          unfolding closure_def by simp
        with cutoff_support False show False by blast
      qed
      show ?thesis using False cutoff_zero
        by (simp add: slp_restrict_field_def)
    qed
  qed
  show ?thesis
  proof (rule exI[of _ ?C], rule conjI[OF C_positive])
    show "\<forall>tau c coefficient multiplier M.
        2 \<le> tau \<and>
        (\<forall>y. y \<in> X \<longrightarrow>
          Real_Vector_Spaces.norm (y - c) \<le> R) \<and>
        aim_complex_lp_on_plane b coefficient \<and>
        {x. coefficient x \<noteq> 0} \<subseteq> Y \<and>
        multiplier \<in> borel_measurable lborel \<and>
        (AE x in lborel. norm (multiplier x) \<le> M) \<and>
        0 \<le> M
        \<longrightarrow>
        (\<lambda>z :: slp_point.
          ereal (Real_Vector_Spaces.norm
            (slp_restrict_field X
              (slp_dbar_psi_inverse (- tau) c
                (\<lambda>x. cutoff x *
                  slp_partial_psi_inverse (- tau) c
                    (\<lambda>y. coefficient y * multiplier y) x)) z)))
          \<in> borel_measurable (lborel :: slp_point measure)
        \<and>
        esssup (lborel :: slp_point measure)
          (\<lambda>z :: slp_point.
            ereal (Real_Vector_Spaces.norm
              (slp_restrict_field X
                (slp_dbar_psi_inverse (- tau) c
                  (\<lambda>x. cutoff x *
                    slp_partial_psi_inverse (- tau) c
                      (\<lambda>y. coefficient y * multiplier y) x)) z)))
          \<le> ereal
            (?C * inverse (sqrt tau) * ln (2 + tau) * M *
              aim_complex_lp_norm b coefficient)"
    proof (intro allI impI)
      fix tau :: real and c :: slp_point
        and coefficient multiplier :: slp_scalar_field and M :: real
      assume data:
        "2 \<le> tau \<and>
          (\<forall>y. y \<in> X \<longrightarrow>
            Real_Vector_Spaces.norm (y - c) \<le> R) \<and>
          aim_complex_lp_on_plane b coefficient \<and>
          {x. coefficient x \<noteq> 0} \<subseteq> Y \<and>
          multiplier \<in> borel_measurable lborel \<and>
          (AE x in lborel. norm (multiplier x) \<le> M) \<and>
          0 \<le> M"
      have tau_lower: "2 \<le> tau" using data by blast
      have relative_radius:
          "\<And>y :: slp_point. y \<in> X \<Longrightarrow>
            Real_Vector_Spaces.norm (y - c) \<le> R"
        using data by blast
      have coefficient_lp: "aim_complex_lp_on_plane b coefficient"
        using data by blast
      have coefficient_carrier: "{x. coefficient x \<noteq> 0} \<subseteq> Y"
        using data by blast
      have multiplier_measurable:
          "multiplier \<in> borel_measurable lborel"
        using data by blast
      have multiplier_bound: "AE x in lborel. norm (multiplier x) \<le> M"
        using data by blast
      have M_nonnegative: "0 \<le> M" using data by blast
      let ?source = "\<lambda>x. coefficient x * multiplier x"
      let ?u = "\<lambda>x. cutoff x * slp_partial_psi_inverse (- tau) c ?source x"
      let ?Du = "\<lambda>x. \<chi> i.
        cutoff x *
          slp_partial_inverse_gradient
            (slp_oscillatory_modulation (- tau) c ?source) x $ i +
        slp_partial_psi_inverse (- tau) c ?source x *
          slp_complex_partial_derivative cutoff i x"
      let ?T = "slp_dbar_psi_inverse (- tau) c ?u"
      note product = slp_complex_lp_AE_bounded_multiplier[
        where p=b and multiplier=multiplier and f=coefficient and C=M,
        OF exponent_positive multiplier_measurable multiplier_bound
          M_nonnegative coefficient_lp]
      have source_lp: "aim_complex_lp_on_plane b ?source"
        using product(1) by (simp only: mult.commute)
      have source_carrier: "{x. ?source x \<noteq> 0} \<subseteq> Y"
        using coefficient_carrier by auto
      have source_support: "bounded {x. ?source x \<noteq> 0}"
        by (rule bounded_subset[OF Y_bounded source_carrier])
      note zero_pairs = slp_both_inner_cauchy_mult_test_w1p_zero_pairs[
        OF evans_density exponent_lower X_open X_bounded source_lp
          source_support cutoff_test]
      have zero_pair: "slp_w1p_zero_pair_on b X ?u ?Du"
        by (rule conjunct2[OF zero_pairs])
      note inner = inner_gain[OF coefficient_lp coefficient_carrier
        multiplier_measurable multiplier_bound M_nonnegative]
      have inner_bound:
          "slp_w1p_norm_on b X ?u ?Du \<le>
            K * M * aim_complex_lp_norm b coefficient"
        by (rule conjunct2[OF inner])
      have restrict_u: "slp_restrict_field X ?u = ?u"
        by (rule restrict_cutoff_product)
      note rough =
        slp_qstar_centered_smooth_far_hls_context.slp_w1p_zero_pair_negative_dbar_psi_inverse_rough_zero_extended_esssup_natural_log_bound[
          OF outer_context tau_lower exponent_above_two radius_nonnegative
            radius_lower set_radius relative_radius X_measurable zero_pair]
      have output_measurable:
          "(\<lambda>z :: slp_point.
            ereal (Real_Vector_Spaces.norm
              (slp_restrict_field X ?T z)))
            \<in> borel_measurable (lborel :: slp_point measure)"
        using rough(1) by (simp only: restrict_u)
      let ?W = "slp_w1p_norm_on b X ?u ?Du"
      let ?M0 = "?L * (192 * ?W)"
      let ?N0 = "?P * ?M0 * ?H"
      let ?B0r = "2 * ?M0"
      let ?DB0r = "?L * (2 * (4 * ?W))"
      let ?CB0r = "((?P * slp_global_cutoff_L) * ?M0) * ?H"
      let ?C0r =
        "?N0 + (?B0r + (?DB0r + (?CB0r + ?P * ?M0 * ?I)))"
      let ?C1r = "?P * ?M0 * ?J"
      let ?rate = "inverse (sqrt tau) * ln (2 + tau)"
      have rough_bound:
          "esssup (lborel :: slp_point measure)
              (\<lambda>z :: slp_point.
                ereal (Real_Vector_Spaces.norm
                  (slp_restrict_field X ?T z)))
            \<le> ereal
              (?rate *
                (?C0r / ln 2 + ?C1r * ((2 + log 2 R) / ln 2)))"
        using rough(2)
        unfolding Let_def
        by (simp only: restrict_u)
      have bracket_factor:
          "?C0r / ln 2 + ?C1r * ((2 + log 2 R) / ln 2) =
            ?RawFactor * ?W"
        by (simp add: algebra_simps)
      have W_nonnegative: "0 \<le> ?W"
        unfolding slp_w1p_norm_on_def by simp
      have G0_le_G: "?RawFactor \<le> ?SafeFactor"
      proof (rule order_trans[OF abs_ge_self])
        show "abs ?RawFactor \<le> ?SafeFactor" by simp
      qed
      have bracket_le:
          "?C0r / ln 2 + ?C1r * ((2 + log 2 R) / ln 2) \<le>
            ?SafeFactor * ?W"
        using mult_right_mono[OF G0_le_G W_nonnegative]
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
      have rough_scaled:
          "?rate *
              (?C0r / ln 2 + ?C1r * ((2 + log 2 R) / ln 2))
            \<le> ?rate * (?SafeFactor * ?W)"
        by (rule mult_left_mono[OF bracket_le rate_nonnegative])
      have ereal_rough_scaled:
          "ereal
              (?rate *
                (?C0r / ln 2 + ?C1r * ((2 + log 2 R) / ln 2)))
            \<le> ereal (?rate * (?SafeFactor * ?W))"
        using rough_scaled by simp
      have outer_G_bound:
          "esssup (lborel :: slp_point measure)
              (\<lambda>z :: slp_point.
                ereal (Real_Vector_Spaces.norm
                  (slp_restrict_field X ?T z)))
            \<le> ereal (?rate * (?SafeFactor * ?W))"
        by (rule order_trans[OF rough_bound ereal_rough_scaled])
      have scale_nonnegative: "0 \<le> ?rate * ?SafeFactor"
        by (rule mult_nonneg_nonneg[OF rate_nonnegative G_nonnegative])
      have inner_scaled:
          "?rate * ?SafeFactor * ?W \<le>
            ?rate * ?SafeFactor *
              (K * M * aim_complex_lp_norm b coefficient)"
        by (rule mult_left_mono[OF inner_bound scale_nonnegative])
      have real_bound:
          "?rate * (?SafeFactor * ?W) \<le>
            ?C * inverse (sqrt tau) * ln (2 + tau) * M *
              aim_complex_lp_norm b coefficient"
        using inner_scaled by (simp add: algebra_simps)
      have ereal_real_bound:
          "ereal (?rate * (?SafeFactor * ?W)) \<le>
            ereal
              (?C * inverse (sqrt tau) * ln (2 + tau) * M *
                aim_complex_lp_norm b coefficient)"
        using real_bound by simp
      have final_bound:
          "esssup (lborel :: slp_point measure)
              (\<lambda>z :: slp_point.
                ereal (Real_Vector_Spaces.norm
                  (slp_restrict_field X ?T z)))
            \<le> ereal
              (?C * inverse (sqrt tau) * ln (2 + tau) * M *
                aim_complex_lp_norm b coefficient)"
        by (rule order_trans[OF outer_G_bound ereal_real_bound])
      show
          "(\<lambda>z :: slp_point.
            ereal (Real_Vector_Spaces.norm
              (slp_restrict_field X ?T z)))
            \<in> borel_measurable (lborel :: slp_point measure)
          \<and>
          esssup (lborel :: slp_point measure)
              (\<lambda>z :: slp_point.
                ereal (Real_Vector_Spaces.norm
                  (slp_restrict_field X ?T z)))
            \<le> ereal
              (?C * inverse (sqrt tau) * ln (2 + tau) * M *
                aim_complex_lp_norm b coefficient)"
        by (rule conjI[OF output_measurable final_bound])
    qed
  qed
qed

end

end
