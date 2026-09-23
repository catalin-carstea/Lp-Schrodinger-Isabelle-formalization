theory Inverse_Schrodinger_Lp_Natural_Logarithmic_Parameter_Comparison
  imports Inverse_Schrodinger_Lp_Logarithmic_Parameter_Comparison
begin

section \<open>Natural-logarithm normalization\<close>

lemma slp_log_sqrt_parameter_natural_bound:
  fixes R tau :: real
  assumes R_lower: "1 \<le> R"
    and tau_lower: "2 \<le> tau"
  shows "1 + log 2 (R * sqrt tau) \<le>
    ((2 + log 2 R) / ln 2) * ln (2 + tau)"
proof -
  note base_two = slp_log_sqrt_parameter_base_two_bound[OF
      R_lower tau_lower]
  have normalization:
      "(2 + log 2 R) * log 2 (2 + tau) =
        ((2 + log 2 R) / ln 2) * ln (2 + tau)"
    by (simp add: log_def algebra_simps)
  show ?thesis
    using base_two by (simp only: normalization)
qed

end
