theory Inverse_Schrodinger_Lp_Nested_Coefficient_Product_Right_Balanced_Esssup
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_015.Inverse_Schrodinger_Lp_Nested_Coefficient_Product_Low_Esssup"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_016.Inverse_Schrodinger_Lp_Nested_Coefficient_Product_Right_High_Esssup"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_015.Inverse_Schrodinger_Lp_Nested_Coefficient_Difference_Pointwise"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_015.Inverse_Schrodinger_Lp_Quantitative_Value_Split_Norms"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_015.Inverse_Schrodinger_Lp_Interpolation_Balancing_Threshold"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Balanced actual right nested coefficient endpoint\<close>

context slp_cauchy_local_w1s
begin

theorem slp_nested_coefficient_product_balanced_right_esssup_bound:
  fixes p a b theta A R A0 B0 B1 :: real
    and X Y :: "slp_point set"
    and cutoff :: slp_scalar_field
  assumes riesz_hls: "aim_planar_riesz_hls_claim"
    and cauchy_test_left_inverse:
      "aim_planar_cauchy_test_left_inverse_claim"
    and evans_density: "evans_compact_support_w1p_zero_density_claim"
    and exponent_a_lower: "1 < a"
    and exponent_a_below_p: "a < p"
    and exponent_p_upper: "p < 2"
    and exponent_b_above_two: "2 < b"
    and interpolation_identity:
      "1 / p = (1 - theta) / a + theta / b"
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
        aim_complex_lp_on_plane p coefficient \<and>
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
            (C * M *
              (inverse (sqrt tau) * ln (2 + tau)) powr theta *
              aim_complex_lp_norm p coefficient))"
proof -
  have exponent_p_lower: "1 < p"
    using exponent_a_lower exponent_a_below_p by linarith
  have exponent_p_positive: "0 < p"
    using exponent_p_lower by linarith
  have exponent_a_positive: "0 < a"
    using exponent_a_lower by linarith
  have exponent_a_upper: "a < 2"
    using exponent_a_below_p exponent_p_upper by linarith
  have exponent_p_below_b: "p < b"
    using exponent_p_upper exponent_b_above_two by linarith
  have X_measurable: "X \<in> sets lborel"
    using X_open by simp

  obtain Cp :: real where Cp_positive: "0 < Cp"
    and endpoint_p:
      "\<forall>tau c coefficient multiplier M.
        aim_complex_lp_on_plane p coefficient \<and>
        multiplier \<in> borel_measurable lborel \<and>
        (AE x in lborel. norm (multiplier x) \<le> M) \<and>
        0 \<le> M
        \<longrightarrow>
        (\<lambda>z :: slp_point.
          ereal (Real_Vector_Spaces.norm
            (slp_restrict_field X
              (slp_partial_psi_inverse tau c
                (\<lambda>x. cutoff x *
                  slp_dbar_psi_inverse tau c
                    (\<lambda>y. coefficient y * multiplier y) x)) z)))
          \<in> borel_measurable (lborel :: slp_point measure) \<and>
        esssup (lborel :: slp_point measure)
          (\<lambda>z :: slp_point.
            ereal (Real_Vector_Spaces.norm
              (slp_restrict_field X
                (slp_partial_psi_inverse tau c
                  (\<lambda>x. cutoff x *
                    slp_dbar_psi_inverse tau c
                      (\<lambda>y. coefficient y * multiplier y) x)) z)))
          \<le> ereal (Cp * M * aim_complex_lp_norm p coefficient) \<and>
        (\<lambda>z :: slp_point.
          ereal (Real_Vector_Spaces.norm
            (slp_restrict_field X
              (slp_dbar_psi_inverse (- tau) c
                (\<lambda>x. cutoff x *
                  slp_partial_psi_inverse (- tau) c
                    (\<lambda>y. coefficient y * multiplier y) x)) z)))
          \<in> borel_measurable (lborel :: slp_point measure) \<and>
        esssup (lborel :: slp_point measure)
          (\<lambda>z :: slp_point.
            ereal (Real_Vector_Spaces.norm
              (slp_restrict_field X
                (slp_dbar_psi_inverse (- tau) c
                  (\<lambda>x. cutoff x *
                    slp_partial_psi_inverse (- tau) c
                      (\<lambda>y. coefficient y * multiplier y) x)) z)))
          \<le> ereal (Cp * M * aim_complex_lp_norm p coefficient)"
    using slp_both_nested_coefficient_product_low_esssup_bounds[
      OF exponent_p_lower exponent_p_upper X_measurable X_bounded cutoff_test]
    by blast
  obtain Ca :: real where Ca_positive: "0 < Ca"
    and endpoint_a:
      "\<forall>tau c coefficient multiplier M.
        aim_complex_lp_on_plane a coefficient \<and>
        multiplier \<in> borel_measurable lborel \<and>
        (AE x in lborel. norm (multiplier x) \<le> M) \<and>
        0 \<le> M
        \<longrightarrow>
        (\<lambda>z :: slp_point.
          ereal (Real_Vector_Spaces.norm
            (slp_restrict_field X
              (slp_partial_psi_inverse tau c
                (\<lambda>x. cutoff x *
                  slp_dbar_psi_inverse tau c
                    (\<lambda>y. coefficient y * multiplier y) x)) z)))
          \<in> borel_measurable (lborel :: slp_point measure) \<and>
        esssup (lborel :: slp_point measure)
          (\<lambda>z :: slp_point.
            ereal (Real_Vector_Spaces.norm
              (slp_restrict_field X
                (slp_partial_psi_inverse tau c
                  (\<lambda>x. cutoff x *
                    slp_dbar_psi_inverse tau c
                      (\<lambda>y. coefficient y * multiplier y) x)) z)))
          \<le> ereal (Ca * M * aim_complex_lp_norm a coefficient) \<and>
        (\<lambda>z :: slp_point.
          ereal (Real_Vector_Spaces.norm
            (slp_restrict_field X
              (slp_dbar_psi_inverse (- tau) c
                (\<lambda>x. cutoff x *
                  slp_partial_psi_inverse (- tau) c
                    (\<lambda>y. coefficient y * multiplier y) x)) z)))
          \<in> borel_measurable (lborel :: slp_point measure) \<and>
        esssup (lborel :: slp_point measure)
          (\<lambda>z :: slp_point.
            ereal (Real_Vector_Spaces.norm
              (slp_restrict_field X
                (slp_dbar_psi_inverse (- tau) c
                  (\<lambda>x. cutoff x *
                    slp_partial_psi_inverse (- tau) c
                      (\<lambda>y. coefficient y * multiplier y) x)) z)))
          \<le> ereal (Ca * M * aim_complex_lp_norm a coefficient)"
    using slp_both_nested_coefficient_product_low_esssup_bounds[
      OF exponent_a_lower exponent_a_upper X_measurable X_bounded cutoff_test]
    by blast
  obtain Cb :: real where Cb_positive: "0 < Cb"
    and endpoint_b:
      "\<forall>tau c coefficient multiplier M.
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
          \<in> borel_measurable (lborel :: slp_point measure) \<and>
        esssup (lborel :: slp_point measure)
          (\<lambda>z :: slp_point.
            ereal (Real_Vector_Spaces.norm
              (slp_restrict_field X
                (slp_dbar_psi_inverse (- tau) c
                  (\<lambda>x. cutoff x *
                    slp_partial_psi_inverse (- tau) c
                      (\<lambda>y. coefficient y * multiplier y) x)) z)))
          \<le> ereal
            (Cb * inverse (sqrt tau) * ln (2 + tau) * M *
              aim_complex_lp_norm b coefficient)"
    using slp_nested_coefficient_product_right_high_esssup_bound[
      OF riesz_hls cauchy_test_left_inverse evans_density
        exponent_b_above_two radius_nonnegative radius_lower set_radius
        X_open X_bounded Y_bounded cutoff_test cutoff_bound
        cutoff_derivative_zero_bound cutoff_derivative_one_bound
        A0_nonnegative B0_nonnegative B1_nonnegative]
    by blast

  have C_positive: "0 < Ca + Cb"
    using Ca_positive Cb_positive by linarith
  show ?thesis
  proof (rule exI[of _ "Ca + Cb"], rule conjI[OF C_positive],
      intro allI impI)
    fix tau :: real and c :: slp_point
      and coefficient multiplier :: slp_scalar_field and M :: real
    assume inputs:
      "2 \<le> tau \<and>
        (\<forall>y. y \<in> X \<longrightarrow>
          Real_Vector_Spaces.norm (y - c) \<le> R) \<and>
        aim_complex_lp_on_plane p coefficient \<and>
        {x. coefficient x \<noteq> 0} \<subseteq> Y \<and>
        multiplier \<in> borel_measurable lborel \<and>
        (AE x in lborel. norm (multiplier x) \<le> M) \<and>
        0 \<le> M"
    have tau_lower: "2 \<le> tau" using inputs by blast
    have center_radius:
        "\<forall>y. y \<in> X \<longrightarrow>
          Real_Vector_Spaces.norm (y - c) \<le> R"
      using inputs by blast
    have coefficient_lp: "aim_complex_lp_on_plane p coefficient"
      using inputs by blast
    have coefficient_support: "{x. coefficient x \<noteq> 0} \<subseteq> Y"
      using inputs by blast
    have multiplier_measurable:
        "multiplier \<in> borel_measurable lborel"
      using inputs by blast
    have multiplier_bound: "AE x in lborel. norm (multiplier x) \<le> M"
      using inputs by blast
    have M_nonnegative: "0 \<le> M" using inputs by blast
    let ?rate = "inverse (sqrt tau) * ln (2 + tau)"
    let ?F = "aim_complex_lp_norm p coefficient"
    have tau_positive: "0 < tau"
      using tau_lower by linarith
    have inverse_sqrt_positive: "0 < inverse (sqrt tau)"
      using tau_positive by simp
    have ln_parameter_positive: "0 < ln (2 + tau)"
    proof (rule ln_gt_zero)
      show "(1::real) < 2 + tau"
        using tau_lower by linarith
    qed
    have rate_positive: "0 < ?rate"
      by (rule mult_pos_pos[OF inverse_sqrt_positive ln_parameter_positive])
    have F_nonnegative: "0 \<le> ?F"
      unfolding aim_complex_lp_norm_def by (rule powr_ge_zero)
    obtain T :: real where T_positive: "0 < T"
      and high_scalar_bound:
        "T powr (1 - p / a) * ?F powr (p / a) \<le>
          ?rate powr theta * ?F"
      and low_scalar_bound:
        "?rate * T powr (1 - p / b) * ?F powr (p / b) \<le>
          ?rate powr theta * ?F"
      using slp_interpolation_balancing_threshold[
        OF exponent_a_positive exponent_a_below_p exponent_p_below_b
          interpolation_identity rate_positive F_nonnegative]
      by (elim exE conjE) assumption+
    let ?low = "slp_value_low_part T coefficient"
    let ?high = "slp_value_high_part T coefficient"
    note split = slp_quantitative_value_split_norm_bounds[
      OF exponent_a_positive exponent_a_below_p exponent_p_below_b
        T_positive coefficient_lp]
    have split_identity: "\<forall>x. coefficient x = ?low x + ?high x"
      using split by blast
    have high_a: "aim_complex_lp_on_plane a ?high"
      using split by blast
    have low_b: "aim_complex_lp_on_plane b ?low"
      using split by blast
    have high_norm_bound:
        "aim_complex_lp_norm a ?high \<le>
          T powr (1 - p / a) * ?F powr (p / a)"
      using split by blast
    have low_norm_bound:
        "aim_complex_lp_norm b ?low \<le>
          T powr (1 - p / b) * ?F powr (p / b)"
      using split by blast
    have coefficient_measurable:
        "coefficient \<in> borel_measurable lborel"
      using coefficient_lp unfolding aim_complex_lp_on_plane_def by blast
    let ?E = "{x. norm (coefficient x) \<le> T}"
    have E_measurable: "?E \<in> sets lborel"
      using coefficient_measurable by measurable
    have restricted_low:
        "slp_restrict_field ?E coefficient = ?low"
      by (rule ext)
        (simp add: slp_restrict_field_def slp_value_low_part_def)
    have low_p: "aim_complex_lp_on_plane p ?low"
    proof -
      have "aim_complex_lp_on_plane p
          (slp_restrict_field ?E coefficient)"
        by (rule slp_restriction_lp_norm_contraction(1)[OF
              exponent_p_positive E_measurable coefficient_lp])
      then show ?thesis by (simp only: restricted_low)
    qed
    have high_p: "aim_complex_lp_on_plane p ?high"
      unfolding slp_value_high_part_def
      by (rule aim_complex_lp_on_plane_diff[
            OF exponent_p_positive coefficient_lp low_p])
    have low_support: "{x. ?low x \<noteq> 0} \<subseteq> Y"
      using coefficient_support
      unfolding slp_value_low_part_def by auto

    let ?whole =
      "\<lambda>z. slp_dbar_psi_inverse (- tau) c
        (\<lambda>x. cutoff x *
          slp_partial_psi_inverse (- tau) c
            (\<lambda>y. coefficient y * multiplier y) x) z"
    let ?low_output =
      "\<lambda>z. slp_dbar_psi_inverse (- tau) c
        (\<lambda>x. cutoff x *
          slp_partial_psi_inverse (- tau) c
            (\<lambda>y. ?low y * multiplier y) x) z"
    let ?high_output =
      "\<lambda>z. slp_dbar_psi_inverse (- tau) c
        (\<lambda>x. cutoff x *
          slp_partial_psi_inverse (- tau) c
            (\<lambda>y. ?high y * multiplier y) x) z"
    let ?whole_restricted = "slp_restrict_field X ?whole"
    let ?low_restricted = "slp_restrict_field X ?low_output"
    let ?high_restricted = "slp_restrict_field X ?high_output"
    let ?h = "\<lambda>z. ereal (Real_Vector_Spaces.norm (?whole_restricted z))"
    let ?h_low =
      "\<lambda>z. ereal (Real_Vector_Spaces.norm (?low_restricted z))"
    let ?h_high =
      "\<lambda>z. ereal (Real_Vector_Spaces.norm (?high_restricted z))"

    have whole_endpoint:
        "?h \<in> borel_measurable (lborel :: slp_point measure) \<and>
          esssup (lborel :: slp_point measure) ?h \<le>
            ereal (Cp * M * ?F)"
      using endpoint_p coefficient_lp multiplier_measurable multiplier_bound
        M_nonnegative by blast
    have high_endpoint:
        "?h_high \<in> borel_measurable (lborel :: slp_point measure) \<and>
          esssup (lborel :: slp_point measure) ?h_high \<le>
            ereal (Ca * M * aim_complex_lp_norm a ?high)"
      using endpoint_a high_a multiplier_measurable multiplier_bound
        M_nonnegative by blast
    have low_endpoint:
        "?h_low \<in> borel_measurable (lborel :: slp_point measure) \<and>
          esssup (lborel :: slp_point measure) ?h_low \<le>
            ereal
              (Cb * inverse (sqrt tau) * ln (2 + tau) * M *
                aim_complex_lp_norm b ?low)"
      using endpoint_b tau_lower center_radius low_b low_support
        multiplier_measurable multiplier_bound M_nonnegative by blast
    have pointwise_context: "aim_planar_riesz_hls_cauchy"
      using riesz_hls aim_planar_hls_cauchy by unfold_locales
    have operator_difference:
        "\<forall>z\<in>X. ?high_output z = ?whole z - ?low_output z"
      using aim_planar_riesz_hls_cauchy.slp_both_nested_coefficient_difference_pointwise[
          OF pointwise_context exponent_p_lower exponent_p_upper X_bounded
            cutoff_test coefficient_lp low_p multiplier_measurable
            multiplier_bound M_nonnegative,
          where tau=tau and c=c]
      unfolding slp_value_high_part_def by blast
    have operator_split: "\<forall>z\<in>X. ?whole z = ?low_output z + ?high_output z"
      using operator_difference by auto
    have restricted_split:
        "?whole_restricted z = ?low_restricted z + ?high_restricted z"
      for z
    proof (cases "z \<in> X")
      case True
      then show ?thesis
        using operator_split
        by (simp add: slp_restrict_field_def)
    next
      case False
      then show ?thesis by (simp add: slp_restrict_field_def)
    qed
    have pointwise_norm_bound: "?h z \<le> ?h_low z + ?h_high z" for z
    proof -
      have norm_bound:
          "Real_Vector_Spaces.norm (?whole_restricted z) \<le>
            Real_Vector_Spaces.norm (?low_restricted z) +
              Real_Vector_Spaces.norm (?high_restricted z)"
        using norm_triangle_ineq[of "?low_restricted z" "?high_restricted z"]
        by (simp only: restricted_split)
      show ?thesis using norm_bound by simp
    qed

    have high_balanced:
        "aim_complex_lp_norm a ?high \<le> ?rate powr theta * ?F"
      by (rule order_trans[OF high_norm_bound high_scalar_bound])
    have low_rate_balanced:
        "?rate * aim_complex_lp_norm b ?low \<le> ?rate powr theta * ?F"
    proof (rule order_trans)
      show "?rate * aim_complex_lp_norm b ?low \<le>
          ?rate * (T powr (1 - p / b) * ?F powr (p / b))"
        by (rule mult_left_mono[OF low_norm_bound])
          (use rate_positive in simp)
      show "?rate * (T powr (1 - p / b) * ?F powr (p / b)) \<le>
          ?rate powr theta * ?F"
        using low_scalar_bound by (simp add: algebra_simps)
    qed
    have CaM_nonnegative: "0 \<le> Ca * M"
      by (rule mult_nonneg_nonneg)
        (use Ca_positive M_nonnegative in linarith)+
    have CbM_nonnegative: "0 \<le> Cb * M"
      by (rule mult_nonneg_nonneg)
        (use Cb_positive M_nonnegative in linarith)+
    have high_real_bound:
        "Ca * M * aim_complex_lp_norm a ?high \<le>
          Ca * M * (?rate powr theta * ?F)"
      by (rule mult_left_mono[OF high_balanced CaM_nonnegative])
    have low_real_bound:
        "Cb * inverse (sqrt tau) * ln (2 + tau) * M *
            aim_complex_lp_norm b ?low
          \<le> Cb * M * (?rate powr theta * ?F)"
      using mult_left_mono[OF low_rate_balanced CbM_nonnegative]
      by (simp add: algebra_simps)
    have sum_real_identity:
        "Cb * M * (?rate powr theta * ?F) +
            Ca * M * (?rate powr theta * ?F) =
          (Ca + Cb) * M * ?rate powr theta * ?F"
      by (simp add: algebra_simps)

    have target_esssup:
        "esssup (lborel :: slp_point measure) ?h \<le>
          ereal ((Ca + Cb) * M * ?rate powr theta * ?F)"
    proof (rule order_trans)
      show "esssup (lborel :: slp_point measure) ?h \<le>
          esssup (lborel :: slp_point measure) (\<lambda>z. ?h_low z + ?h_high z)"
        by (rule esssup_mono[OF conjunct1[OF whole_endpoint]
              pointwise_norm_bound])
      show "esssup (lborel :: slp_point measure)
            (\<lambda>z. ?h_low z + ?h_high z) \<le>
          ereal ((Ca + Cb) * M * ?rate powr theta * ?F)"
      proof (rule order_trans[OF esssup_add])
        have low_esssup:
            "esssup (lborel :: slp_point measure) ?h_low \<le>
              ereal (Cb * M * (?rate powr theta * ?F))"
          by (rule order_trans[OF conjunct2[OF low_endpoint]])
            (use low_real_bound in simp)
        have high_esssup:
            "esssup (lborel :: slp_point measure) ?h_high \<le>
              ereal (Ca * M * (?rate powr theta * ?F))"
          by (rule order_trans[OF conjunct2[OF high_endpoint]])
            (use high_real_bound in simp)
        show "esssup (lborel :: slp_point measure) ?h_low +
              esssup (lborel :: slp_point measure) ?h_high \<le>
            ereal ((Ca + Cb) * M * ?rate powr theta * ?F)"
          using add_mono[OF low_esssup high_esssup]
            sum_real_identity by simp
      qed
    qed
    show
        "(\<lambda>z :: slp_point.
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
            ((Ca + Cb) * M *
              (inverse (sqrt tau) * ln (2 + tau)) powr theta *
              aim_complex_lp_norm p coefficient)"
      using conjunct1[OF whole_endpoint] target_esssup by blast
  qed
qed

end

end
