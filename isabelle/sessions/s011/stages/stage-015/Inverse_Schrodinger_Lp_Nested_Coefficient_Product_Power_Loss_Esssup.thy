theory Inverse_Schrodinger_Lp_Nested_Coefficient_Product_Power_Loss_Esssup
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_015.Inverse_Schrodinger_Lp_Nested_Coefficient_Product_Balanced_Esssup"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_015.Inverse_Schrodinger_Lp_Interpolation_Exponent_Selection"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Absorption of the logarithmic interpolation loss\<close>

lemma slp_logarithmic_interpolation_power_absorption:
  fixes theta eta :: real
  assumes theta_positive: "0 < theta"
    and eta_positive: "0 < eta"
  shows
    "\<exists>K::real. 0 < K \<and>
      (\<forall>tau. 2 \<le> tau \<longrightarrow>
        (inverse (sqrt tau) * ln (2 + tau)) powr theta
          \<le> K * tau powr (- theta / 2 + eta))"
proof -
  let ?d = "eta / theta"
  let ?K = "(2 powr eta) / (?d powr theta)"
  have theta_nonzero: "theta \<noteq> 0"
    using theta_positive by linarith
  have d_positive: "0 < ?d"
    using eta_positive theta_positive by simp
  have d_nonnegative: "0 \<le> ?d"
    using d_positive by linarith
  have d_nonzero: "?d \<noteq> 0"
    using d_positive by linarith
  have d_theta: "?d * theta = eta"
    using eta_positive theta_positive by simp
  have denominator_positive: "0 < ?d powr theta"
    using d_nonzero by simp
  have K_positive: "0 < ?K"
    using denominator_positive by simp

  show ?thesis
  proof (intro exI[of _ ?K] conjI allI impI)
    show "0 < ?K"
      by (rule K_positive)
  next
    fix tau :: real
    assume tau_lower: "2 \<le> tau"
    have tau_positive: "0 < tau"
      using tau_lower by linarith
    have tau_nonnegative: "0 \<le> tau"
      using tau_positive by linarith
    have tau_at_least_one: "1 \<le> tau"
      using tau_lower by linarith
    have parameter_at_least_one: "1 \<le> 2 + tau"
      using tau_lower by linarith
    have parameter_positive: "0 < 2 + tau"
      using tau_lower by linarith
    have logarithm_nonnegative: "0 \<le> ln (2 + tau)"
      using parameter_at_least_one by simp

    have parameter_linear_bound: "2 + tau \<le> 2 * tau"
      using tau_lower by linarith
    have parameter_power_bound:
        "(2 + tau) powr ?d \<le> (2 * tau) powr ?d"
      by (rule powr_mono2[OF d_nonnegative])
        (use parameter_positive parameter_linear_bound in linarith)+
    have logarithm_power_bound:
        "ln (2 + tau) \<le> ((2 * tau) powr ?d) / ?d"
    proof -
      have "ln (2 + tau) \<le> ((2 + tau) powr ?d) / ?d"
        by (rule ln_powr_bound[OF parameter_at_least_one d_positive])
      also have "... \<le> ((2 * tau) powr ?d) / ?d"
        by (rule divide_right_mono[OF parameter_power_bound d_nonnegative])
      finally show ?thesis .
    qed
    have logarithm_raised_bound:
        "ln (2 + tau) powr theta
          \<le> (((2 * tau) powr ?d) / ?d) powr theta"
      by (rule powr_mono2[OF less_imp_le[OF theta_positive]
            logarithm_nonnegative logarithm_power_bound])
    have logarithm_raised_normalization:
        "(((2 * tau) powr ?d) / ?d) powr theta
          = ?K * tau powr eta"
    proof -
      have "(((2 * tau) powr ?d) / ?d) powr theta
          = (2 * tau) powr (?d * theta) / (?d powr theta)"
        by (simp only: powr_divide powr_powr)
      also have "... = (2 * tau) powr eta / (?d powr theta)"
        by (simp only: d_theta)
      also have "... = ?K * tau powr eta"
        by (simp only: powr_mult divide_inverse mult.assoc mult.commute
              mult.left_commute)
      finally show ?thesis .
    qed
    have logarithm_final:
        "ln (2 + tau) powr theta \<le> ?K * tau powr eta"
      using logarithm_raised_bound
      by (simp only: logarithm_raised_normalization)

    have inverse_sqrt_power:
        "(inverse (sqrt tau)) powr theta = tau powr (- theta / 2)"
    proof -
      have sqrt_power: "sqrt tau = tau powr (1 / 2)"
        using powr_half_sqrt[OF tau_nonnegative] by (rule sym)
      have half_theta: "(1 / 2) * theta = theta / 2"
        by (simp only: divide_inverse mult.left_neutral mult.commute)
      have "(inverse (sqrt tau)) powr theta
          = inverse ((tau powr (1 / 2)) powr theta)"
        by (simp only: inverse_powr sqrt_power)
      also have "... = inverse (tau powr ((1 / 2) * theta))"
        by (simp only: powr_powr)
      also have "... = inverse (tau powr (theta / 2))"
        by (simp only: half_theta)
      also have "... = tau powr (- theta / 2)"
        by (simp only: divide_minus_left powr_minus)
      finally show ?thesis .
    qed
    have leading_nonnegative: "0 \<le> tau powr (- theta / 2)"
      by (rule powr_ge_zero)
    have rate_power_normalization:
        "(inverse (sqrt tau) * ln (2 + tau)) powr theta
          = tau powr (- theta / 2) * ln (2 + tau) powr theta"
      by (simp only: powr_mult inverse_sqrt_power)
    have "(inverse (sqrt tau) * ln (2 + tau)) powr theta
        \<le> tau powr (- theta / 2) * (?K * tau powr eta)"
      unfolding rate_power_normalization
      by (rule mult_left_mono[OF logarithm_final leading_nonnegative])
    also have "... = ?K * tau powr (- theta / 2 + eta)"
      by (simp only: powr_add mult.assoc mult.commute mult.left_commute)
    finally show
      "(inverse (sqrt tau) * ln (2 + tau)) powr theta
        \<le> ?K * tau powr (- theta / 2 + eta)" .
  qed
qed

section \<open>Actual left endpoint with the manuscript power loss\<close>

context slp_cauchy_local_w1s
begin

theorem slp_nested_coefficient_product_left_esssup_power_loss_bound:
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
              (slp_partial_psi_inverse tau c
                (\<lambda>x. cutoff x *
                  slp_dbar_psi_inverse tau c
                    (\<lambda>y. coefficient y * multiplier y) x)) z)))
          \<in> borel_measurable (lborel :: slp_point measure)
        \<and>
        esssup (lborel :: slp_point measure)
          (\<lambda>z :: slp_point.
            ereal (Real_Vector_Spaces.norm
              (slp_restrict_field X
                (slp_partial_psi_inverse tau c
                  (\<lambda>x. cutoff x *
                    slp_dbar_psi_inverse tau c
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
              (slp_partial_psi_inverse tau c
                (\<lambda>x. cutoff x *
                  slp_dbar_psi_inverse tau c
                    (\<lambda>y. coefficient y * multiplier y) x)) z)))
          \<in> borel_measurable (lborel :: slp_point measure)
        \<and>
        esssup (lborel :: slp_point measure)
          (\<lambda>z :: slp_point.
            ereal (Real_Vector_Spaces.norm
              (slp_restrict_field X
                (slp_partial_psi_inverse tau c
                  (\<lambda>x. cutoff x *
                    slp_dbar_psi_inverse tau c
                      (\<lambda>y. coefficient y * multiplier y) x)) z)))
          \<le> ereal
            (C0 * M *
              (inverse (sqrt tau) * ln (2 + tau)) powr theta *
              aim_complex_lp_norm p coefficient)"
    using slp_nested_coefficient_product_balanced_left_esssup_bound[
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
              (slp_partial_psi_inverse tau c
                (\<lambda>x. cutoff x *
                  slp_dbar_psi_inverse tau c
                    (\<lambda>y. coefficient y * multiplier y) x)) z)))
          \<in> borel_measurable (lborel :: slp_point measure)
        \<and>
        esssup (lborel :: slp_point measure)
          (\<lambda>z :: slp_point.
            ereal (Real_Vector_Spaces.norm
              (slp_restrict_field X
                (slp_partial_psi_inverse tau c
                  (\<lambda>x. cutoff x *
                    slp_dbar_psi_inverse tau c
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
              (slp_partial_psi_inverse tau c
                (\<lambda>x. cutoff x *
                  slp_dbar_psi_inverse tau c
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
              (slp_partial_psi_inverse tau c
                (\<lambda>x. cutoff x *
                  slp_dbar_psi_inverse tau c
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
              (slp_partial_psi_inverse tau c
                (\<lambda>x. cutoff x *
                  slp_dbar_psi_inverse tau c
                    (\<lambda>y. coefficient y * multiplier y) x)) z)))
          \<in> borel_measurable (lborel :: slp_point measure)
        \<and>
        esssup (lborel :: slp_point measure)
          (\<lambda>z :: slp_point.
            ereal (Real_Vector_Spaces.norm
              (slp_restrict_field X
                (slp_partial_psi_inverse tau c
                  (\<lambda>x. cutoff x *
                    slp_dbar_psi_inverse tau c
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
