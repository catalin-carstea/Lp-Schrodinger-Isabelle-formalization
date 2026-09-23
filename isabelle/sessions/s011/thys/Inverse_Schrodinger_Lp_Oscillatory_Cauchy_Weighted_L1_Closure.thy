theory Inverse_Schrodinger_Lp_Oscillatory_Cauchy_Weighted_L1_Closure
  imports Inverse_Schrodinger_Lp_Cauchy_Weighted_L1_Continuity
begin

section \<open>Weighted-L1 smooth-to-rough oscillatory identity\<close>

context aim_planar_cauchy_test_left_inverse
begin

theorem slp_partial_inverse_oscillatory_divided_weighted_L1_closure:
  assumes tau_pos: "0 < tau"
    and phi_test: "\<And>n. slp_test_function_on UNIV (phi n)"
    and base_target_integrable:
      "slp_cauchy_integrable_at SLP_Partial_Inverse
        (\<lambda>x. (slp_point_as_complex (x - c) *
          slp_center_kernel tau c x) * g x) z"
    and derivative_target_integrable:
      "slp_cauchy_integrable_at SLP_Partial_Inverse
        (\<lambda>x. slp_center_kernel tau c x * dg x) z"
    and pointwise_limit: "((\<lambda>n. phi n z) \<longlongrightarrow> g z) sequentially"
    and base_weighted_L1:
      "((\<lambda>n. \<integral>\<^sup>+y.
          norm (slp_cauchy_integrand SLP_Partial_Inverse
            (\<lambda>x. (slp_point_as_complex (x - c) *
                slp_center_kernel tau c x) * phi n x -
              (slp_point_as_complex (x - c) *
                slp_center_kernel tau c x) * g x) z y) \<partial>lborel)
        \<longlongrightarrow> 0) sequentially"
    and derivative_weighted_L1:
      "((\<lambda>n. \<integral>\<^sup>+y.
          norm (slp_cauchy_integrand SLP_Partial_Inverse
            (\<lambda>x. slp_center_kernel tau c x *
                slp_classical_wirtinger_partial (phi n) x -
              slp_center_kernel tau c x * dg x) z y) \<partial>lborel)
        \<longlongrightarrow> 0) sequentially"
  shows "slp_partial_inverse
      (\<lambda>x. (slp_point_as_complex (x - c) *
        slp_center_kernel tau c x) * g x) z =
    (1 / (\<i> * of_real tau)) *
      (slp_center_kernel tau c z * g z -
        slp_partial_inverse
          (\<lambda>x. slp_center_kernel tau c x * dg x) z)"
proof -
  have base_source_integrable:
      "\<And>n. slp_cauchy_integrable_at SLP_Partial_Inverse
        (\<lambda>x. (slp_point_as_complex (x - c) *
          slp_center_kernel tau c x) * phi n x) z"
  proof -
    fix n
    have source_test: "slp_test_function_on UNIV
        (\<lambda>x. (slp_point_as_complex (x - c) *
          slp_center_kernel tau c x) * phi n x)"
      by (rule slp_center_coordinate_amplitude_test_function[OF phi_test])
    show "slp_cauchy_integrable_at SLP_Partial_Inverse
        (\<lambda>x. (slp_point_as_complex (x - c) *
          slp_center_kernel tau c x) * phi n x) z"
      by (rule slp_test_function_cauchy_integrable_at[OF source_test])
  qed
  have derivative_source_integrable:
      "\<And>n. slp_cauchy_integrable_at SLP_Partial_Inverse
        (\<lambda>x. slp_center_kernel tau c x *
          slp_classical_wirtinger_partial (phi n) x) z"
  proof -
    fix n
    have source_test: "slp_test_function_on UNIV
        (\<lambda>x. slp_center_kernel tau c x *
          slp_classical_wirtinger_partial (phi n) x)"
      by (rule slp_oscillatory_derivative_summands_test_function(1)[OF
            phi_test])
    show "slp_cauchy_integrable_at SLP_Partial_Inverse
        (\<lambda>x. slp_center_kernel tau c x *
          slp_classical_wirtinger_partial (phi n) x) z"
      by (rule slp_test_function_cauchy_integrable_at[OF source_test])
  qed
  have base_limit:
      "((\<lambda>n. slp_partial_inverse
          (\<lambda>x. (slp_point_as_complex (x - c) *
            slp_center_kernel tau c x) * phi n x) z)
        \<longlongrightarrow> slp_partial_inverse
          (\<lambda>x. (slp_point_as_complex (x - c) *
            slp_center_kernel tau c x) * g x) z) sequentially"
    by (rule slp_partial_inverse_tendsto_of_weighted_L1[OF
          base_source_integrable base_target_integrable base_weighted_L1])
  have value_limit:
      "((\<lambda>n. slp_center_kernel tau c z * phi n z)
        \<longlongrightarrow> slp_center_kernel tau c z * g z) sequentially"
    by (rule tendsto_mult_left[OF pointwise_limit])
  have derivative_limit:
      "((\<lambda>n. slp_partial_inverse
          (\<lambda>x. slp_center_kernel tau c x *
            slp_classical_wirtinger_partial (phi n) x) z)
        \<longlongrightarrow> slp_partial_inverse
          (\<lambda>x. slp_center_kernel tau c x * dg x) z) sequentially"
    by (rule slp_partial_inverse_tendsto_of_weighted_L1[OF
          derivative_source_integrable derivative_target_integrable
          derivative_weighted_L1])
  show ?thesis
    by (rule slp_partial_inverse_oscillatory_divided_sequential_closure[OF
          tau_pos phi_test base_limit value_limit derivative_limit])
qed

end

end
