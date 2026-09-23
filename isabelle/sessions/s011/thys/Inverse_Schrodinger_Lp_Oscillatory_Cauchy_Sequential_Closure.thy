theory Inverse_Schrodinger_Lp_Oscillatory_Cauchy_Sequential_Closure
  imports Inverse_Schrodinger_Lp_Oscillatory_Cauchy_Division
begin

section \<open>Sequential closure of the divided smooth identity\<close>

context aim_planar_cauchy_test_left_inverse
begin

theorem slp_partial_inverse_oscillatory_divided_sequential_closure:
  assumes tau_pos: "0 < tau"
    and phi_test: "\<And>n. slp_test_function_on UNIV (phi n)"
    and base_limit:
      "((\<lambda>n. slp_partial_inverse
          (\<lambda>x. (slp_point_as_complex (x - c) *
            slp_center_kernel tau c x) * phi n x) z)
        \<longlongrightarrow> base_limit_value) sequentially"
    and value_limit:
      "((\<lambda>n. slp_center_kernel tau c z * phi n z)
        \<longlongrightarrow> value_limit_value) sequentially"
    and derivative_limit:
      "((\<lambda>n. slp_partial_inverse
          (\<lambda>x. slp_center_kernel tau c x *
            slp_classical_wirtinger_partial (phi n) x) z)
        \<longlongrightarrow> derivative_limit_value) sequentially"
  shows "base_limit_value =
    (1 / (\<i> * of_real tau)) *
      (value_limit_value - derivative_limit_value)"
proof -
  let ?lhs = "\<lambda>n. slp_partial_inverse
    (\<lambda>x. (slp_point_as_complex (x - c) *
      slp_center_kernel tau c x) * phi n x) z"
  let ?rhs = "\<lambda>n. (1 / (\<i> * of_real tau)) *
    (slp_center_kernel tau c z * phi n z -
      slp_partial_inverse
        (\<lambda>x. slp_center_kernel tau c x *
          slp_classical_wirtinger_partial (phi n) x) z)"
  have pointwise: "?lhs n = ?rhs n" for n
    by (rule slp_partial_inverse_oscillatory_divided[OF tau_pos phi_test])
  have functions_equal: "?lhs = ?rhs"
    by (rule ext) (rule pointwise)
  have difference_limit:
    "((\<lambda>n. slp_center_kernel tau c z * phi n z -
        slp_partial_inverse
          (\<lambda>x. slp_center_kernel tau c x *
            slp_classical_wirtinger_partial (phi n) x) z)
      \<longlongrightarrow> value_limit_value - derivative_limit_value)
      sequentially"
    by (rule tendsto_diff[OF value_limit derivative_limit])
  have right_limit:
    "(?rhs \<longlongrightarrow>
      (1 / (\<i> * of_real tau)) *
        (value_limit_value - derivative_limit_value)) sequentially"
    by (rule tendsto_mult_left[OF difference_limit])
  have right_base_limit: "(?rhs \<longlongrightarrow> base_limit_value) sequentially"
    using base_limit by (simp only: functions_equal)
  show ?thesis
    by (rule tendsto_unique[
          OF trivial_limit_sequentially right_base_limit right_limit])
qed

end

end
