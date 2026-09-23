theory Inverse_Schrodinger_Lp_Qstar_Smooth_Fixed_Terminal_Gain
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_010.Inverse_Schrodinger_Lp_Qstar_Smooth_Terminal_Exponent_HLS"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_One_Sided_Cauchy_Principal_Decay"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Oscillatory_Test_Closure"
begin

section \<open>Fixed compact-smooth terminal qstar gain\<close>

context slp_qstar_centered_smooth_far_hls_context
begin

theorem slp_qstar_smooth_fixed_terminal_gain:
  fixes s :: real and f :: slp_scalar_field
  assumes s_lower: "2 < s"
    and f_test: "slp_test_function_on UNIV f"
  shows
    "\<exists>K::real. 0 < K \<and>
      (\<forall>tau R c.
        2 \<le> tau \<and> 1 \<le> R * sqrt tau \<and>
        (\<forall>y. f y \<noteq> 0 \<longrightarrow> norm (y - c) \<le> R)
        \<longrightarrow>
        aim_complex_lp_on_plane s (slp_partial_psi_inverse tau c f) \<and>
        aim_complex_lp_on_plane s (slp_dbar_psi_inverse tau c f) \<and>
        aim_complex_lp_norm s (slp_partial_psi_inverse tau c f)
          \<le> K * inverse (sqrt tau) \<and>
        aim_complex_lp_norm s (slp_dbar_psi_inverse tau c f)
          \<le> K * inverse (sqrt tau))"
proof -
  have s_positive: "0 < s"
    using s_lower by linarith
  have source_lower: "1 < slp_hls_source_exponent s"
    and source_upper: "slp_hls_source_exponent s < 2"
    using slp_hls_source_exponent_bounds[OF s_lower] by auto
  have source_positive: "0 < slp_hls_source_exponent s"
    using source_lower by linarith
  have f_membership: "aim_complex_lp_on_plane s f"
    by (rule slp_test_function_aim_complex_lp_on_plane[OF s_positive f_test])
  have derivative_test:
      "slp_test_function_on UNIV (slp_classical_wirtinger_partial f)"
    by (rule slp_classical_wirtinger_partial_test_function[OF f_test])
  have derivative_membership:
      "aim_complex_lp_on_plane (slp_hls_source_exponent s)
        (slp_classical_wirtinger_partial f)"
    by (rule slp_test_function_aim_complex_lp_on_plane[OF source_positive
          derivative_test])
  let ?g = "\<lambda>x. cnj (f x)"
  have conjugate_test: "slp_test_function_on UNIV ?g"
    using f_test by simp
  have conjugate_derivative_test:
      "slp_test_function_on UNIV (slp_classical_wirtinger_partial ?g)"
    by (rule slp_classical_wirtinger_partial_test_function[OF conjugate_test])
  have conjugate_derivative_membership:
      "aim_complex_lp_on_plane (slp_hls_source_exponent s)
        (slp_classical_wirtinger_partial ?g)"
    by (rule slp_test_function_aim_complex_lp_on_plane[OF source_positive
          conjugate_derivative_test])
  obtain C::real where C_positive: "0 < C"
    and terminal:
      "\<And>s tau R c f.
        2 < s \<Longrightarrow> 2 \<le> tau \<Longrightarrow>
        1 \<le> R * sqrt tau \<Longrightarrow>
        slp_test_function_on UNIV f \<Longrightarrow>
        aim_complex_lp_on_plane s f \<Longrightarrow>
        aim_complex_lp_on_plane (slp_hls_source_exponent s)
          (slp_classical_wirtinger_partial f) \<Longrightarrow>
        aim_complex_lp_on_plane (slp_hls_source_exponent s)
          (slp_classical_wirtinger_partial (\<lambda>x. cnj (f x))) \<Longrightarrow>
        (\<And>y. f y \<noteq> 0 \<Longrightarrow> norm (y - c) \<le> R) \<Longrightarrow>
        aim_complex_lp_on_plane s (slp_partial_psi_inverse tau c f) \<and>
        aim_complex_lp_on_plane s (slp_dbar_psi_inverse tau c f) \<and>
        aim_complex_lp_norm s (slp_partial_psi_inverse tau c f)
          \<le> C /
              ((slp_hls_source_exponent s - 1) *
                (2 - slp_hls_source_exponent s)) *
              inverse (sqrt tau) *
            (2 * aim_complex_lp_norm s f +
              aim_complex_lp_norm (slp_hls_source_exponent s)
                (slp_classical_wirtinger_partial f)) \<and>
        aim_complex_lp_norm s (slp_dbar_psi_inverse tau c f)
          \<le> C /
              ((slp_hls_source_exponent s - 1) *
                (2 - slp_hls_source_exponent s)) *
              inverse (sqrt tau) *
            (2 * aim_complex_lp_norm s f +
              aim_complex_lp_norm (slp_hls_source_exponent s)
                (slp_classical_wirtinger_partial (\<lambda>x. cnj (f x))))"
    using slp_qstar_smooth_terminal_exponent_inverse_sqrt_hls by blast
  let ?B_partial =
    "C /
      ((slp_hls_source_exponent s - 1) *
        (2 - slp_hls_source_exponent s)) *
      (2 * aim_complex_lp_norm s f +
        aim_complex_lp_norm (slp_hls_source_exponent s)
          (slp_classical_wirtinger_partial f))"
  let ?B_dbar =
    "C /
      ((slp_hls_source_exponent s - 1) *
        (2 - slp_hls_source_exponent s)) *
      (2 * aim_complex_lp_norm s f +
        aim_complex_lp_norm (slp_hls_source_exponent s)
          (slp_classical_wirtinger_partial (\<lambda>x. cnj (f x))))"
  let ?K = "max 1 (max ?B_partial ?B_dbar)"
  have K_positive: "0 < ?K"
    by simp
  have partial_coefficient_le: "?B_partial \<le> ?K"
    by simp
  have dbar_coefficient_le: "?B_dbar \<le> ?K"
    by simp
  show ?thesis
  proof (intro exI[of _ ?K] conjI allI impI)
    show "0 < ?K"
      by (rule K_positive)
    fix tau R c
    assume hypotheses:
      "2 \<le> tau \<and> 1 \<le> R * sqrt tau \<and>
        (\<forall>y. f y \<noteq> 0 \<longrightarrow> norm (y - c) \<le> R)"
    from hypotheses have tau_lower: "2 \<le> tau"
      and normalized_lower: "1 \<le> R * sqrt tau"
      and support: "\<And>y. f y \<noteq> 0 \<Longrightarrow> norm (y - c) \<le> R"
      by blast+
    have terminal_data:
        "aim_complex_lp_on_plane s (slp_partial_psi_inverse tau c f) \<and>
          aim_complex_lp_on_plane s (slp_dbar_psi_inverse tau c f) \<and>
          aim_complex_lp_norm s (slp_partial_psi_inverse tau c f)
            \<le> C /
                ((slp_hls_source_exponent s - 1) *
                  (2 - slp_hls_source_exponent s)) *
                inverse (sqrt tau) *
              (2 * aim_complex_lp_norm s f +
                aim_complex_lp_norm (slp_hls_source_exponent s)
                  (slp_classical_wirtinger_partial f)) \<and>
          aim_complex_lp_norm s (slp_dbar_psi_inverse tau c f)
            \<le> C /
                ((slp_hls_source_exponent s - 1) *
                  (2 - slp_hls_source_exponent s)) *
                inverse (sqrt tau) *
              (2 * aim_complex_lp_norm s f +
                aim_complex_lp_norm (slp_hls_source_exponent s)
                  (slp_classical_wirtinger_partial (\<lambda>x. cnj (f x))))"
      by (rule terminal[OF s_lower tau_lower normalized_lower f_test
            f_membership derivative_membership
            conjugate_derivative_membership support])
    have tau_positive: "0 < tau"
      using tau_lower by linarith
    have inverse_sqrt_nonnegative: "0 \<le> inverse (sqrt tau)"
      using tau_positive by simp
    have partial_base:
        "aim_complex_lp_norm s (slp_partial_psi_inverse tau c f)
          \<le> ?B_partial * inverse (sqrt tau)"
      using terminal_data[THEN conjunct2, THEN conjunct2, THEN conjunct1]
      by (simp only: mult.assoc mult.commute mult.left_commute)
    have dbar_base:
        "aim_complex_lp_norm s (slp_dbar_psi_inverse tau c f)
          \<le> ?B_dbar * inverse (sqrt tau)"
      using terminal_data[THEN conjunct2, THEN conjunct2, THEN conjunct2]
      by (simp only: mult.assoc mult.commute mult.left_commute)
    have partial_scaled:
        "?B_partial * inverse (sqrt tau) \<le> ?K * inverse (sqrt tau)"
      by (rule mult_right_mono[OF partial_coefficient_le
            inverse_sqrt_nonnegative])
    have dbar_scaled:
        "?B_dbar * inverse (sqrt tau) \<le> ?K * inverse (sqrt tau)"
      by (rule mult_right_mono[OF dbar_coefficient_le
            inverse_sqrt_nonnegative])
    show "aim_complex_lp_on_plane s (slp_partial_psi_inverse tau c f)"
      by (rule terminal_data[THEN conjunct1])
    show "aim_complex_lp_on_plane s (slp_dbar_psi_inverse tau c f)"
      by (rule terminal_data[THEN conjunct2, THEN conjunct1])
    show "aim_complex_lp_norm s (slp_partial_psi_inverse tau c f)
        \<le> ?K * inverse (sqrt tau)"
      by (rule order_trans[OF partial_base partial_scaled])
    show "aim_complex_lp_norm s (slp_dbar_psi_inverse tau c f)
        \<le> ?K * inverse (sqrt tau)"
      by (rule order_trans[OF dbar_base dbar_scaled])
  qed
qed

end

end
