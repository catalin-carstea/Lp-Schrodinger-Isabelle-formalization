theory Inverse_Schrodinger_Lp_Oscillatory_Cauchy_Power_Error_Closure
  imports Inverse_Schrodinger_Lp_Cauchy_Power_Error
begin

section \<open>Power-error closure of the rough oscillatory identity\<close>

definition slp_oscillatory_base_approximation_error ::
    "real \<Rightarrow> slp_point \<Rightarrow>
      (nat \<Rightarrow> slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      nat \<Rightarrow> slp_point \<Rightarrow> complex" where
  "slp_oscillatory_base_approximation_error tau c phi g n x =
    (slp_point_as_complex (x - c) * slp_center_kernel tau c x) * phi n x -
    (slp_point_as_complex (x - c) * slp_center_kernel tau c x) * g x"

definition slp_oscillatory_derivative_approximation_error ::
    "real \<Rightarrow> slp_point \<Rightarrow>
      (nat \<Rightarrow> slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      nat \<Rightarrow> slp_point \<Rightarrow> complex" where
  "slp_oscillatory_derivative_approximation_error tau c phi dg n x =
    slp_center_kernel tau c x *
        slp_classical_wirtinger_partial (phi n) x -
    slp_center_kernel tau c x * dg x"

context aim_planar_cauchy_test_left_inverse
begin

theorem slp_partial_inverse_oscillatory_divided_power_error_closure:
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
    and base_lp:
      "\<And>n. aim_complex_lp_on_plane b
        (slp_oscillatory_base_approximation_error tau c phi g n)"
    and base_support:
      "\<And>n y. slp_oscillatory_base_approximation_error
          tau c phi g n y \<noteq> 0 \<Longrightarrow> norm (z - y) \<le> R"
    and base_power_error:
      "((\<lambda>n. \<integral>y. norm
          (slp_oscillatory_base_approximation_error tau c phi g n y)
            powr b \<partial>lborel) \<longlongrightarrow> 0) sequentially"
    and derivative_lp:
      "\<And>n. aim_complex_lp_on_plane b
        (slp_oscillatory_derivative_approximation_error tau c phi dg n)"
    and derivative_support:
      "\<And>n y. slp_oscillatory_derivative_approximation_error
          tau c phi dg n y \<noteq> 0 \<Longrightarrow> norm (z - y) \<le> R"
    and derivative_power_error:
      "((\<lambda>n. \<integral>y. norm
          (slp_oscillatory_derivative_approximation_error tau c phi dg n y)
            powr b \<partial>lborel) \<longlongrightarrow> 0) sequentially"
  shows "slp_partial_inverse
      (\<lambda>x. (slp_point_as_complex (x - c) *
        slp_center_kernel tau c x) * g x) z =
    (1 / (\<i> * of_real tau)) *
      (slp_center_kernel tau c z * g z -
        slp_partial_inverse
          (\<lambda>x. slp_center_kernel tau c x * dg x) z)"
proof -
  have base_weighted_L1:
      "((\<lambda>n. \<integral>\<^sup>+y.
          norm (slp_cauchy_integrand SLP_Partial_Inverse
            (slp_oscillatory_base_approximation_error tau c phi g n)
            z y) \<partial>lborel) \<longlongrightarrow> 0) sequentially"
    by (rule slp_cauchy_weighted_L1_tendsto_of_power_error[OF
          exponent radius_nonnegative base_lp base_support base_power_error])
  have derivative_weighted_L1:
      "((\<lambda>n. \<integral>\<^sup>+y.
          norm (slp_cauchy_integrand SLP_Partial_Inverse
            (slp_oscillatory_derivative_approximation_error
              tau c phi dg n) z y) \<partial>lborel)
        \<longlongrightarrow> 0) sequentially"
    by (rule slp_cauchy_weighted_L1_tendsto_of_power_error[OF
          exponent radius_nonnegative derivative_lp derivative_support
          derivative_power_error])
  show ?thesis
  proof (rule slp_partial_inverse_oscillatory_divided_weighted_L1_closure[OF
          tau_pos phi_test base_target_integrable
          derivative_target_integrable pointwise_limit])
    show "((\<lambda>n. \<integral>\<^sup>+y.
        norm (slp_cauchy_integrand SLP_Partial_Inverse
          (\<lambda>x. (slp_point_as_complex (x - c) *
              slp_center_kernel tau c x) * phi n x -
            (slp_point_as_complex (x - c) *
              slp_center_kernel tau c x) * g x) z y) \<partial>lborel)
      \<longlongrightarrow> 0) sequentially"
      using base_weighted_L1
      unfolding slp_oscillatory_base_approximation_error_def .
    show "((\<lambda>n. \<integral>\<^sup>+y.
        norm (slp_cauchy_integrand SLP_Partial_Inverse
          (\<lambda>x. slp_center_kernel tau c x *
              slp_classical_wirtinger_partial (phi n) x -
            slp_center_kernel tau c x * dg x) z y) \<partial>lborel)
      \<longlongrightarrow> 0) sequentially"
      using derivative_weighted_L1
      unfolding slp_oscillatory_derivative_approximation_error_def .
  qed
qed

end

end
