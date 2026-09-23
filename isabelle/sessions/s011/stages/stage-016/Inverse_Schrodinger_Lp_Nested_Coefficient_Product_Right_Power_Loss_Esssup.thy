theory Inverse_Schrodinger_Lp_Nested_Coefficient_Product_Right_Power_Loss_Esssup
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_015.Inverse_Schrodinger_Lp_Nested_Coefficient_Product_Power_Loss_Esssup"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_016.Inverse_Schrodinger_Lp_Nested_Coefficient_Product_Right_Balanced_Esssup"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Actual right endpoint with the manuscript power loss\<close>

context slp_cauchy_local_w1s
begin

theorem slp_nested_coefficient_product_right_esssup_power_loss_bound:
  fixes p epsilon A R A0 B0 B1 :: real
    and X Y :: "slp_point set"
    and cutoff :: slp_scalar_field
  assumes riesz_hls: "aim_planar_riesz_hls_claim"
    and cauchy_test_left_inverse:
      "aim_planar_cauchy_test_left_inverse_claim"
    and evans_density: "evans_compact_support_w1p_zero_density_claim"
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
              tau powr (-(1 - 1 / p) + epsilon) *
              aim_complex_lp_norm p coefficient))"
proof -
  have half_loss_positive: "0 < epsilon / 2"
    using loss_positive by linarith
  obtain a b theta :: real where
      a_lower: "1 < a"
    and a_below_p: "a < p"
    and p_below_two: "p < 2"
    and b_above_two: "2 < b"
    and theta_positive: "0 < theta"
    and theta_below_one: "theta < 1"
    and interpolation_identity:
      "1 / p = (1 - theta) / a + theta / b"
    and rate_gap:
      "1 - 1 / p - epsilon / 2 < theta / 2"
    using slp_interpolation_exponents[OF exponent_lower exponent_upper
          half_loss_positive]
    by blast

  obtain C0 :: real where C0_positive: "0 < C0"
    and balanced_endpoint:
      "\<forall>tau c coefficient multiplier M.
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
            (C0 * M *
              (inverse (sqrt tau) * ln (2 + tau)) powr theta *
              aim_complex_lp_norm p coefficient)"
    using slp_nested_coefficient_product_balanced_right_esssup_bound[
        OF riesz_hls cauchy_test_left_inverse evans_density
          a_lower a_below_p p_below_two b_above_two interpolation_identity
          radius_nonnegative radius_lower set_radius X_open X_bounded
          Y_bounded cutoff_test cutoff_bound cutoff_derivative_zero_bound
          cutoff_derivative_one_bound A0_nonnegative B0_nonnegative
          B1_nonnegative]
    by blast

  obtain K :: real where K_positive: "0 < K"
    and scalar_absorption:
      "\<forall>tau. 2 \<le> tau \<longrightarrow>
        (inverse (sqrt tau) * ln (2 + tau)) powr theta
          \<le> K * tau powr (- theta / 2 + epsilon / 2)"
    using slp_logarithmic_interpolation_power_absorption[
        OF theta_positive half_loss_positive]
    by blast

  let ?C = "C0 * K"
  have C_positive: "0 < ?C"
    using C0_positive K_positive by (rule mult_pos_pos)
  show ?thesis
  proof (rule exI[of _ ?C], rule conjI[OF C_positive], intro allI impI)
    fix tau :: real and c :: slp_point
      and coefficient multiplier :: slp_scalar_field and M :: real
    assume endpoint_input:
      "2 \<le> tau \<and>
        (\<forall>y. y \<in> X \<longrightarrow>
          Real_Vector_Spaces.norm (y - c) \<le> R) \<and>
        aim_complex_lp_on_plane p coefficient \<and>
        {x. coefficient x \<noteq> 0} \<subseteq> Y \<and>
        multiplier \<in> borel_measurable lborel \<and>
        (AE x in lborel. norm (multiplier x) \<le> M) \<and>
        0 \<le> M"
    then have tau_lower: "2 \<le> tau"
      and M_nonnegative: "0 \<le> M"
      by blast+
    have tau_at_least_one: "1 \<le> tau"
      using tau_lower by linarith
    have coefficient_norm_nonnegative:
        "0 \<le> aim_complex_lp_norm p coefficient"
      unfolding aim_complex_lp_norm_def by (rule powr_ge_zero)
    have endpoint_result:
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
            (C0 * M *
              (inverse (sqrt tau) * ln (2 + tau)) powr theta *
              aim_complex_lp_norm p coefficient)"
      using balanced_endpoint endpoint_input by blast
    have exponent_order:
        "- theta / 2 + epsilon / 2
          \<le> -(1 - 1 / p) + epsilon"
      using rate_gap by linarith
    have parameter_power_mono:
        "tau powr (- theta / 2 + epsilon / 2)
          \<le> tau powr (-(1 - 1 / p) + epsilon)"
      by (rule powr_mono[OF exponent_order tau_at_least_one])
    have absorbed_rate:
        "(inverse (sqrt tau) * ln (2 + tau)) powr theta
          \<le> K * tau powr (-(1 - 1 / p) + epsilon)"
    proof -
      have "(inverse (sqrt tau) * ln (2 + tau)) powr theta
          \<le> K * tau powr (- theta / 2 + epsilon / 2)"
        using scalar_absorption tau_lower by blast
      also have "... \<le> K * tau powr (-(1 - 1 / p) + epsilon)"
        by (rule mult_left_mono[OF parameter_power_mono
              less_imp_le[OF K_positive]])
      finally show ?thesis .
    qed
    have C0_nonnegative: "0 \<le> C0"
      using C0_positive by linarith
    have left_factor_nonnegative: "0 \<le> C0 * M"
      by (rule mult_nonneg_nonneg[OF C0_nonnegative M_nonnegative])
    have real_bound:
        "C0 * M *
            (inverse (sqrt tau) * ln (2 + tau)) powr theta *
            aim_complex_lp_norm p coefficient
          \<le> ?C * M *
            tau powr (-(1 - 1 / p) + epsilon) *
            aim_complex_lp_norm p coefficient"
    proof -
      have "(C0 * M) *
            (inverse (sqrt tau) * ln (2 + tau)) powr theta
          \<le> (C0 * M) *
            (K * tau powr (-(1 - 1 / p) + epsilon))"
        by (rule mult_left_mono[OF absorbed_rate left_factor_nonnegative])
      then have "((C0 * M) *
            (inverse (sqrt tau) * ln (2 + tau)) powr theta) *
            aim_complex_lp_norm p coefficient
          \<le> ((C0 * M) *
            (K * tau powr (-(1 - 1 / p) + epsilon))) *
            aim_complex_lp_norm p coefficient"
        by (rule mult_right_mono[OF _ coefficient_norm_nonnegative])
      then show ?thesis
        by (simp only: mult.assoc mult.commute mult.left_commute)
    qed
    have endpoint_bound:
      "esssup (lborel :: slp_point measure)
        (\<lambda>z :: slp_point.
          ereal (Real_Vector_Spaces.norm
            (slp_restrict_field X
              (slp_dbar_psi_inverse (- tau) c
                (\<lambda>x. cutoff x *
                  slp_partial_psi_inverse (- tau) c
                    (\<lambda>y. coefficient y * multiplier y) x)) z)))
        \<le> ereal
          (C0 * M *
            (inverse (sqrt tau) * ln (2 + tau)) powr theta *
            aim_complex_lp_norm p coefficient)"
      using endpoint_result by blast
    have real_embedded:
      "ereal
          (C0 * M *
            (inverse (sqrt tau) * ln (2 + tau)) powr theta *
            aim_complex_lp_norm p coefficient)
        \<le> ereal
          (?C * M *
            tau powr (-(1 - 1 / p) + epsilon) *
            aim_complex_lp_norm p coefficient)"
      using real_bound by simp
    have target_esssup:
      "esssup (lborel :: slp_point measure)
        (\<lambda>z :: slp_point.
          ereal (Real_Vector_Spaces.norm
            (slp_restrict_field X
              (slp_dbar_psi_inverse (- tau) c
                (\<lambda>x. cutoff x *
                  slp_partial_psi_inverse (- tau) c
                    (\<lambda>y. coefficient y * multiplier y) x)) z)))
        \<le> ereal
          (?C * M *
            tau powr (-(1 - 1 / p) + epsilon) *
            aim_complex_lp_norm p coefficient)"
      using endpoint_bound real_embedded by (rule order_trans)
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
            (?C * M *
              tau powr (-(1 - 1 / p) + epsilon) *
              aim_complex_lp_norm p coefficient)"
      using conjunct1[OF endpoint_result] target_esssup by blast
  qed
qed

end

end
