theory Inverse_Schrodinger_Lp_Raw_Power_Error_Closure
  imports Inverse_Schrodinger_Lp_Base_Error_Power_Limit
begin

section \<open>Oscillatory identity from raw Sobolev approximation errors\<close>

context aim_planar_cauchy_test_left_inverse
begin

theorem slp_partial_inverse_oscillatory_divided_raw_power_error_closure:
  fixes b R :: real
  assumes tau_pos: "0 < tau"
    and exponent: "2 < b"
    and radius_nonnegative: "0 \<le> R"
    and phi_test: "\<And>n. slp_test_function_on UNIV (phi n)"
    and base_target_integrable:
      "slp_cauchy_integrable_at SLP_Partial_Inverse
        (\<lambda>x. (slp_point_as_complex (x - c) *
          slp_center_kernel tau c x) * g x) z"
    and derivative_target_integrable:
      "slp_cauchy_integrable_at SLP_Partial_Inverse
        (\<lambda>x. slp_center_kernel tau c x * dg x) z"
    and pointwise_limit: "((\<lambda>n. phi n z) \<longlongrightarrow> g z) sequentially"
    and raw_base_lp:
      "\<And>n. aim_complex_lp_on_plane b
        (slp_raw_value_approximation_error phi g n)"
    and raw_base_support:
      "\<And>n y. slp_raw_value_approximation_error phi g n y \<noteq> 0
        \<Longrightarrow> norm (z - y) \<le> R"
    and raw_base_power_error:
      "((\<lambda>n. \<integral>y.
        norm (slp_raw_value_approximation_error phi g n y) powr b
          \<partial>lborel) \<longlongrightarrow> 0) sequentially"
    and raw_derivative_lp:
      "\<And>n. aim_complex_lp_on_plane b
        (slp_raw_partial_approximation_error phi dg n)"
    and raw_derivative_support:
      "\<And>n y. slp_raw_partial_approximation_error phi dg n y \<noteq> 0
        \<Longrightarrow> norm (z - y) \<le> R"
    and raw_derivative_power_error:
      "((\<lambda>n. \<integral>y.
        norm (slp_raw_partial_approximation_error phi dg n y) powr b
          \<partial>lborel) \<longlongrightarrow> 0) sequentially"
  shows "slp_partial_inverse
      (\<lambda>x. (slp_point_as_complex (x - c) *
        slp_center_kernel tau c x) * g x) z =
    (1 / (\<i> * of_real tau)) *
      (slp_center_kernel tau c z * g z -
        slp_partial_inverse
          (\<lambda>x. slp_center_kernel tau c x * dg x) z)"
proof -
  have exponent_positive: "0 < b"
    using exponent by linarith
  have base_lp:
      "aim_complex_lp_on_plane b
        (slp_oscillatory_base_approximation_error tau c phi g n)" for n
    by (rule slp_oscillatory_base_approximation_error_lp[OF
          exponent_positive radius_nonnegative raw_base_lp raw_base_support])
  have base_support:
      "slp_oscillatory_base_approximation_error tau c phi g n y \<noteq> 0
        \<Longrightarrow> norm (z - y) \<le> R" for n y
    by (rule slp_oscillatory_base_approximation_error_support[OF
          raw_base_support])
  have base_power_error:
      "((\<lambda>n. \<integral>y. norm
        (slp_oscillatory_base_approximation_error tau c phi g n y) powr b
          \<partial>lborel) \<longlongrightarrow> 0) sequentially"
    by (rule slp_oscillatory_base_approximation_error_power_tendsto_zero[OF
          exponent_positive radius_nonnegative raw_base_lp raw_base_support
          raw_base_power_error])
  have derivative_lp:
      "aim_complex_lp_on_plane b
        (slp_oscillatory_derivative_approximation_error tau c phi dg n)"
      for n
    using raw_derivative_lp[of n] by simp
  have derivative_support:
      "slp_oscillatory_derivative_approximation_error tau c phi dg n y
          \<noteq> 0 \<Longrightarrow> norm (z - y) \<le> R" for n y
    by (rule slp_oscillatory_derivative_approximation_error_support[OF
          raw_derivative_support])
  have derivative_power_error:
      "((\<lambda>n. \<integral>y. norm
        (slp_oscillatory_derivative_approximation_error tau c phi dg n y)
          powr b \<partial>lborel) \<longlongrightarrow> 0) sequentially"
    by (rule
          slp_oscillatory_derivative_approximation_error_power_tendsto_zero[OF
            raw_derivative_power_error])
  show ?thesis
    by (rule slp_partial_inverse_oscillatory_divided_power_error_closure[OF
          tau_pos exponent radius_nonnegative phi_test
          base_target_integrable derivative_target_integrable pointwise_limit
          base_lp base_support base_power_error derivative_lp
          derivative_support derivative_power_error])
qed

end

end
