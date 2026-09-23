theory Inverse_Schrodinger_Lp_Derivative_Error_Transfer
  imports Inverse_Schrodinger_Lp_Approximation_Error_Factorization
begin

section \<open>Norm-one transfer for the derivative approximation error\<close>

lemma slp_oscillatory_derivative_approximation_error_eq_modulation:
  "slp_oscillatory_derivative_approximation_error tau c phi dg n =
    slp_oscillatory_modulation tau c
      (slp_raw_partial_approximation_error phi dg n)"
proof (rule ext)
  fix x
  show "slp_oscillatory_derivative_approximation_error tau c phi dg n x =
      slp_oscillatory_modulation tau c
        (slp_raw_partial_approximation_error phi dg n) x"
    unfolding slp_oscillatory_modulation_def
    by (rule slp_oscillatory_derivative_approximation_error_factorization)
qed

lemma slp_oscillatory_derivative_approximation_error_lp_iff [simp]:
  "aim_complex_lp_on_plane b
      (slp_oscillatory_derivative_approximation_error tau c phi dg n)
    \<longleftrightarrow>
    aim_complex_lp_on_plane b
      (slp_raw_partial_approximation_error phi dg n)"
  by (simp only:
        slp_oscillatory_derivative_approximation_error_eq_modulation
        slp_oscillatory_modulation_lp_iff)

lemma slp_oscillatory_derivative_approximation_error_power_integral:
  "(\<integral>x. norm
      (slp_oscillatory_derivative_approximation_error tau c phi dg n x)
        powr b \<partial>lborel) =
    (\<integral>x. norm (slp_raw_partial_approximation_error phi dg n x)
        powr b \<partial>lborel)"
  by (simp only:
        slp_oscillatory_derivative_approximation_error_eq_modulation
        slp_oscillatory_modulation_norm)

lemma slp_oscillatory_derivative_approximation_error_power_tendsto_zero:
  assumes raw_limit:
    "((\<lambda>n. \<integral>x.
        norm (slp_raw_partial_approximation_error phi dg n x) powr b
          \<partial>lborel) \<longlongrightarrow> 0) sequentially"
  shows "((\<lambda>n. \<integral>x.
      norm (slp_oscillatory_derivative_approximation_error
        tau c phi dg n x) powr b \<partial>lborel)
      \<longlongrightarrow> 0) sequentially"
  using raw_limit
  by (simp only:
        slp_oscillatory_derivative_approximation_error_power_integral)

end
