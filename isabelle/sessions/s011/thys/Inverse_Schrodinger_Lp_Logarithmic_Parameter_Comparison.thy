theory Inverse_Schrodinger_Lp_Logarithmic_Parameter_Comparison
  imports Inverse_Schrodinger_Lp_Near_Far_Annular_Envelope
begin

section \<open>A logarithmic comparison for the parameter choice\<close>

lemma slp_log_sqrt_parameter_base_two_bound:
  fixes R tau :: real
  assumes R_lower: "1 \<le> R"
    and tau_lower: "2 \<le> tau"
  shows "1 + log 2 (R * sqrt tau) \<le>
    (2 + log 2 R) * log 2 (2 + tau)"
proof -
  have R_positive: "0 < R"
    using R_lower by linarith
  have R_nonnegative: "0 \<le> R"
    using R_lower by linarith
  have tau_positive: "0 < tau"
    using tau_lower by linarith
  have tau_nonnegative: "0 \<le> tau"
    using tau_lower by linarith
  have sqrt_tau_positive: "0 < sqrt tau"
    using tau_positive by simp
  have tau_square: "tau \<le> tau\<^sup>2"
  proof -
    have "1 * tau \<le> tau * tau"
      by (rule mult_right_mono[OF _ tau_nonnegative])
         (use tau_lower in linarith)
    then show ?thesis
      by (simp add: power2_eq_square)
  qed
  have sqrt_tau_le_tau: "sqrt tau \<le> tau"
    by (rule real_le_lsqrt[OF tau_nonnegative tau_square])
  have radius_le:
      "R * sqrt tau \<le> R * (2 + tau)"
  proof -
    have first: "R * sqrt tau \<le> R * tau"
      by (rule mult_left_mono[OF sqrt_tau_le_tau R_nonnegative])
    have second: "R * tau \<le> R * (2 + tau)"
      by (rule mult_left_mono[OF _ R_nonnegative]) linarith
    show ?thesis
      by (rule order_trans[OF first second])
  qed
  have log_radius_le:
      "log 2 (R * sqrt tau) \<le> log 2 (R * (2 + tau))"
    by (rule log_mono[OF _ _ radius_le])
       (use R_positive sqrt_tau_positive in \<open>simp_all\<close>)
  have log_product:
      "log 2 (R * (2 + tau)) = log 2 R + log 2 (2 + tau)"
    by (rule log_mult_pos[OF R_positive]) (use tau_lower in linarith)
  have log_R_nonnegative: "0 \<le> log 2 R"
  proof -
    have "log 2 1 \<le> log 2 R"
    proof (rule log_mono)
      show "(1::real) < 2" by simp
      show "(0::real) < 1" by simp
      show "(1::real) \<le> R" by (rule R_lower)
    qed
    then show ?thesis by simp
  qed
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
  have algebraic_bound:
      "1 + (log 2 R + log 2 (2 + tau)) \<le>
        (2 + log 2 R) * log 2 (2 + tau)"
  proof -
    have first_sum:
        "1 + log 2 (2 + tau) \<le>
          log 2 (2 + tau) + log 2 (2 + tau)"
      using log_growth_at_least_one by linarith
    have log_R_product:
        "log 2 R \<le> log 2 R * log 2 (2 + tau)"
    proof -
      have "log 2 R * 1 \<le> log 2 R * log 2 (2 + tau)"
        by (rule mult_left_mono[OF
              log_growth_at_least_one log_R_nonnegative])
      then show ?thesis by simp
    qed
    note combined = add_mono[OF first_sum log_R_product]
    show ?thesis
      using combined by (simp add: algebra_simps)
  qed
  show ?thesis
  proof -
    have first:
        "1 + log 2 (R * sqrt tau) \<le>
          1 + log 2 (R * (2 + tau))"
      using log_radius_le by linarith
    have second:
        "1 + log 2 (R * (2 + tau)) =
          1 + (log 2 R + log 2 (2 + tau))"
      by (simp only: log_product)
    show ?thesis
      using first second algebraic_bound by linarith
  qed
qed

end
