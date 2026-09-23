theory Inverse_Schrodinger_Lp_Approximation_Error_Factorization
  imports Inverse_Schrodinger_Lp_Oscillatory_Cauchy_Power_Error_Closure
begin

section \<open>Raw approximation errors and oscillatory factors\<close>

definition slp_raw_value_approximation_error ::
    "(nat \<Rightarrow> slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      nat \<Rightarrow> slp_point \<Rightarrow> complex" where
  "slp_raw_value_approximation_error phi g n x = phi n x - g x"

definition slp_raw_partial_approximation_error ::
    "(nat \<Rightarrow> slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      nat \<Rightarrow> slp_point \<Rightarrow> complex" where
  "slp_raw_partial_approximation_error phi dg n x =
    slp_classical_wirtinger_partial (phi n) x - dg x"

lemma slp_oscillatory_base_approximation_error_factorization:
  "slp_oscillatory_base_approximation_error tau c phi g n x =
    (slp_point_as_complex (x - c) * slp_center_kernel tau c x) *
      slp_raw_value_approximation_error phi g n x"
  unfolding slp_oscillatory_base_approximation_error_def
    slp_raw_value_approximation_error_def
  by (rule right_diff_distrib[symmetric])

lemma slp_oscillatory_derivative_approximation_error_factorization:
  "slp_oscillatory_derivative_approximation_error tau c phi dg n x =
    slp_center_kernel tau c x *
      slp_raw_partial_approximation_error phi dg n x"
  unfolding slp_oscillatory_derivative_approximation_error_def
    slp_raw_partial_approximation_error_def
  by (rule right_diff_distrib[symmetric])

lemma slp_oscillatory_base_approximation_error_norm:
  "norm (slp_oscillatory_base_approximation_error tau c phi g n x) =
    norm (x - c) * norm (slp_raw_value_approximation_error phi g n x)"
  by (simp only: slp_oscillatory_base_approximation_error_factorization
        norm_mult slp_point_as_complex_norm
        slp_center_kernel_norm mult_1)

lemma slp_oscillatory_derivative_approximation_error_norm:
  "norm (slp_oscillatory_derivative_approximation_error tau c phi dg n x) =
    norm (slp_raw_partial_approximation_error phi dg n x)"
  by (simp only:
        slp_oscillatory_derivative_approximation_error_factorization
        norm_mult slp_center_kernel_norm mult_1_left)

lemma slp_oscillatory_base_approximation_error_support:
  assumes raw_support:
    "slp_raw_value_approximation_error phi g n y \<noteq> 0 \<Longrightarrow>
      norm (z - y) \<le> R"
    and oscillatory_nonzero:
      "slp_oscillatory_base_approximation_error tau c phi g n y \<noteq> 0"
  shows "norm (z - y) \<le> R"
proof (rule raw_support)
  show "slp_raw_value_approximation_error phi g n y \<noteq> 0"
  proof
    assume raw_zero: "slp_raw_value_approximation_error phi g n y = 0"
    have oscillatory_zero:
        "slp_oscillatory_base_approximation_error tau c phi g n y = 0"
    proof -
      have "slp_oscillatory_base_approximation_error tau c phi g n y =
          (slp_point_as_complex (y - c) * slp_center_kernel tau c y) *
            slp_raw_value_approximation_error phi g n y"
        by (rule slp_oscillatory_base_approximation_error_factorization)
      also have "... =
          (slp_point_as_complex (y - c) * slp_center_kernel tau c y) * 0"
        by (simp only: raw_zero)
      also have "... = 0" by (rule mult_zero_right)
      finally show ?thesis .
    qed
    show False by (rule notE[OF oscillatory_nonzero oscillatory_zero])
  qed
qed

lemma slp_oscillatory_derivative_approximation_error_support:
  assumes raw_support:
    "slp_raw_partial_approximation_error phi dg n y \<noteq> 0 \<Longrightarrow>
      norm (z - y) \<le> R"
    and oscillatory_nonzero:
      "slp_oscillatory_derivative_approximation_error tau c phi dg n y
        \<noteq> 0"
  shows "norm (z - y) \<le> R"
proof (rule raw_support)
  show "slp_raw_partial_approximation_error phi dg n y \<noteq> 0"
  proof
    assume raw_zero: "slp_raw_partial_approximation_error phi dg n y = 0"
    have oscillatory_zero:
        "slp_oscillatory_derivative_approximation_error
          tau c phi dg n y = 0"
    proof -
      have "slp_oscillatory_derivative_approximation_error
          tau c phi dg n y =
        slp_center_kernel tau c y *
          slp_raw_partial_approximation_error phi dg n y"
        by (rule slp_oscillatory_derivative_approximation_error_factorization)
      also have "... = slp_center_kernel tau c y * 0"
        by (simp only: raw_zero)
      also have "... = 0" by (rule mult_zero_right)
      finally show ?thesis .
    qed
    show False by (rule notE[OF oscillatory_nonzero oscillatory_zero])
  qed
qed

end
