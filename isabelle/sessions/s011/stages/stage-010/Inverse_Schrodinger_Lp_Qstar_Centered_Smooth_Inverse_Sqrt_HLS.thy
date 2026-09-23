theory Inverse_Schrodinger_Lp_Qstar_Centered_Smooth_Inverse_Sqrt_HLS
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_010.Inverse_Schrodinger_Lp_Qstar_Centered_Smooth_Coarse_HLS"
begin

section \<open>Inverse-square-root cutoff specialization\<close>

lemma slp_qstar_inverse_sqrt_cutoff_balance:
  assumes tau_positive: "0 < tau"
  shows
    "inverse (sqrt tau) * n +
        (1 / (tau * inverse (sqrt tau))) * (n + m) =
      inverse (sqrt tau) * (2 * n + m)"
proof -
  have sqrt_tau_positive: "0 < sqrt tau"
    using tau_positive by simp
  have root_ratio: "sqrt tau / tau = inverse (sqrt tau)"
    by (rule sqrt_divide_self_eq[OF less_imp_le[OF tau_positive]])
  have reciprocal_scale:
      "1 / (tau * inverse (sqrt tau)) = sqrt tau / tau"
    using sqrt_tau_positive
    by (simp add: divide_inverse inverse_mult_distrib mult_ac)
  show ?thesis
    using reciprocal_scale root_ratio by (simp add: algebra_simps)
qed

context slp_qstar_centered_smooth_far_hls_context
begin

theorem slp_qstar_centered_smooth_inverse_sqrt_hls:
  "\<exists>C::real. 0 < C \<and>
    (\<forall>a tau R f.
      1 < a \<and> a < 2 \<and> 2 \<le> tau \<and>
      1 \<le> R * sqrt tau \<and>
      slp_test_function_on UNIV f \<and>
      aim_complex_lp_on_plane (aim_hls_target_exponent a) f \<and>
      aim_complex_lp_on_plane a (slp_classical_wirtinger_partial f) \<and>
      (\<forall>y. f y \<noteq> 0 \<longrightarrow> norm y \<le> R)
      \<longrightarrow>
      aim_complex_lp_on_plane (aim_hls_target_exponent a)
        (slp_partial_psi_inverse tau 0 f) \<and>
      aim_complex_lp_norm (aim_hls_target_exponent a)
          (slp_partial_psi_inverse tau 0 f)
        \<le> C / ((a - 1) * (2 - a)) * inverse (sqrt tau) *
          (2 * aim_complex_lp_norm (aim_hls_target_exponent a) f +
            aim_complex_lp_norm a
              (slp_classical_wirtinger_partial f)))"
proof -
  obtain C::real where C_positive: "0 < C"
    and coarse:
      "\<And>a tau delta R f.
        1 < a \<Longrightarrow> a < 2 \<Longrightarrow> 0 < tau \<Longrightarrow>
        0 < delta \<Longrightarrow> delta \<le> R \<Longrightarrow>
        slp_test_function_on UNIV f \<Longrightarrow>
        aim_complex_lp_on_plane (aim_hls_target_exponent a) f \<Longrightarrow>
        aim_complex_lp_on_plane a
          (slp_classical_wirtinger_partial f) \<Longrightarrow>
        (\<And>y. f y \<noteq> 0 \<Longrightarrow> norm y \<le> R) \<Longrightarrow>
        aim_complex_lp_on_plane (aim_hls_target_exponent a)
          (slp_partial_psi_inverse tau 0 f) \<and>
        aim_complex_lp_norm (aim_hls_target_exponent a)
            (slp_partial_psi_inverse tau 0 f)
          \<le> C / ((a - 1) * (2 - a)) *
            (delta * aim_complex_lp_norm (aim_hls_target_exponent a) f +
              (1 / (tau * delta)) *
                (aim_complex_lp_norm (aim_hls_target_exponent a) f +
                  aim_complex_lp_norm a
                    (slp_classical_wirtinger_partial f)))"
    using slp_qstar_centered_smooth_coarse_hls by blast
  show ?thesis
  proof (intro exI[of _ C] conjI allI impI)
    show "0 < C"
      by (rule C_positive)
    fix a tau R f
    assume hypotheses:
      "1 < a \<and> a < 2 \<and> 2 \<le> tau \<and>
        1 \<le> R * sqrt tau \<and>
        slp_test_function_on UNIV f \<and>
        aim_complex_lp_on_plane (aim_hls_target_exponent a) f \<and>
        aim_complex_lp_on_plane a (slp_classical_wirtinger_partial f) \<and>
        (\<forall>y. f y \<noteq> 0 \<longrightarrow> norm y \<le> R)"
    from hypotheses have a_lower: "1 < a"
      and a_upper: "a < 2"
      and tau_lower: "2 \<le> tau"
      and normalized_lower: "1 \<le> R * sqrt tau"
      and test_function: "slp_test_function_on UNIV f"
      and f_membership:
        "aim_complex_lp_on_plane (aim_hls_target_exponent a) f"
      and derivative_membership:
        "aim_complex_lp_on_plane a
          (slp_classical_wirtinger_partial f)"
      and support: "\<And>y. f y \<noteq> 0 \<Longrightarrow> norm y \<le> R"
      by blast+
    have tau_positive: "0 < tau"
      using tau_lower by linarith
    have delta_positive: "0 < inverse (sqrt tau)"
      using tau_positive by simp
    have delta_nonnegative: "0 \<le> inverse (sqrt tau)"
      using delta_positive by simp
    have delta_le_R: "inverse (sqrt tau) \<le> R"
    proof -
      have scaled:
          "inverse (sqrt tau) * 1 \<le>
            inverse (sqrt tau) * (R * sqrt tau)"
        by (rule mult_left_mono[OF normalized_lower delta_nonnegative])
      show ?thesis
        using scaled tau_positive by (simp add: mult_ac)
    qed
    have total_data:
        "aim_complex_lp_on_plane (aim_hls_target_exponent a)
            (slp_partial_psi_inverse tau 0 f) \<and>
          aim_complex_lp_norm (aim_hls_target_exponent a)
              (slp_partial_psi_inverse tau 0 f)
            \<le> C / ((a - 1) * (2 - a)) *
              (inverse (sqrt tau) *
                  aim_complex_lp_norm (aim_hls_target_exponent a) f +
                (1 / (tau * inverse (sqrt tau))) *
                  (aim_complex_lp_norm (aim_hls_target_exponent a) f +
                    aim_complex_lp_norm a
                      (slp_classical_wirtinger_partial f)))"
      by (rule coarse[OF a_lower a_upper tau_positive delta_positive
            delta_le_R test_function f_membership derivative_membership
            support])
    have total_membership:
        "aim_complex_lp_on_plane (aim_hls_target_exponent a)
          (slp_partial_psi_inverse tau 0 f)"
      by (rule total_data[THEN conjunct1])
    have total_bound:
        "aim_complex_lp_norm (aim_hls_target_exponent a)
            (slp_partial_psi_inverse tau 0 f)
          \<le> C / ((a - 1) * (2 - a)) *
            (inverse (sqrt tau) *
                aim_complex_lp_norm (aim_hls_target_exponent a) f +
              (1 / (tau * inverse (sqrt tau))) *
                (aim_complex_lp_norm (aim_hls_target_exponent a) f +
                  aim_complex_lp_norm a
                    (slp_classical_wirtinger_partial f)))"
      by (rule total_data[THEN conjunct2])
    note balance = slp_qstar_inverse_sqrt_cutoff_balance[
      OF tau_positive,
      where n = "aim_complex_lp_norm (aim_hls_target_exponent a) f"
        and m = "aim_complex_lp_norm a
          (slp_classical_wirtinger_partial f)"]
    show "aim_complex_lp_on_plane (aim_hls_target_exponent a)
        (slp_partial_psi_inverse tau 0 f)"
      by (rule total_membership)
    show "aim_complex_lp_norm (aim_hls_target_exponent a)
          (slp_partial_psi_inverse tau 0 f)
        \<le> C / ((a - 1) * (2 - a)) * inverse (sqrt tau) *
          (2 * aim_complex_lp_norm (aim_hls_target_exponent a) f +
            aim_complex_lp_norm a
              (slp_classical_wirtinger_partial f))"
      using total_bound by (simp only: balance mult.assoc)
  qed
qed

end

end
