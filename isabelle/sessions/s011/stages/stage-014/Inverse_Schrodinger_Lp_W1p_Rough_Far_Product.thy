theory Inverse_Schrodinger_Lp_W1p_Rough_Far_Product
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_014.Inverse_Schrodinger_Lp_W1p_Raw_Error_Support"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Raw_Power_Error_Closure"
begin

section \<open>Rough divided oscillatory far-product identity\<close>

context aim_planar_cauchy_test_left_inverse
begin

theorem slp_w1p_partial_inverse_oscillatory_divided_rough_far_product:
  fixes p R :: real
  assumes tau_positive: "0 < tau"
    and exponent_above_two: "2 < p"
    and radius_nonnegative: "0 \<le> R"
    and phi_test: "\<And>n. slp_test_function_on X (phi n)"
    and error_pairs:
      "\<And>n. slp_w1p_pair_on p X
        (\<lambda>x. phi n x - u x)
        (\<lambda>x. slp_classical_gradient (phi n) x - Du x)"
    and error_norm_tends:
      "((\<lambda>n. slp_w1p_norm_on p X
          (\<lambda>x. phi n x - u x)
          (\<lambda>x. slp_classical_gradient (phi n) x - Du x))
        \<longlongrightarrow> 0) sequentially"
    and X_radius: "\<And>y. y \<in> X \<Longrightarrow> norm (z - y) \<le> R"
    and base_target_integrable:
      "slp_cauchy_integrable_at SLP_Partial_Inverse
        (\<lambda>x. (slp_point_as_complex (x - c) *
          slp_center_kernel tau c x) * slp_restrict_field X u x) z"
    and derivative_target_integrable:
      "slp_cauchy_integrable_at SLP_Partial_Inverse
        (\<lambda>x. slp_center_kernel tau c x *
          slp_restrict_field X (slp_gradient_wirtinger_partial Du) x) z"
    and pointwise_limit:
      "((\<lambda>n. phi n z) \<longlongrightarrow> slp_restrict_field X u z)
        sequentially"
  shows "slp_partial_inverse
      (\<lambda>x. (slp_point_as_complex (x - c) *
        slp_center_kernel tau c x) * slp_restrict_field X u x) z =
    (1 / (\<i> * of_real tau)) *
      (slp_center_kernel tau c z * slp_restrict_field X u z -
        slp_partial_inverse
          (\<lambda>x. slp_center_kernel tau c x *
            slp_restrict_field X
              (slp_gradient_wirtinger_partial Du) x) z)"
proof -
  have exponent_positive: "0 < p"
    using exponent_above_two by linarith
  have exponent_one_le: "1 \<le> p"
    using exponent_above_two by linarith
  note raw_value_data = slp_w1p_raw_restricted_value_and_support_data[
    where p=p and X=X and phi=phi and u=u and Du=Du and z=z and R=R,
    OF exponent_positive phi_test error_pairs error_norm_tends X_radius]
  note raw_derivative_data =
    slp_raw_partial_approximation_error_restricted_wirtinger_data[
      where p=p and X=X and phi=phi and u=u and Du=Du,
      OF exponent_one_le phi_test error_pairs error_norm_tends]
  show ?thesis
    by (rule
        slp_partial_inverse_oscillatory_divided_raw_power_error_closure[
          where b=p and R=R and tau=tau and c=c and phi=phi
            and g="slp_restrict_field X u"
            and dg="slp_restrict_field X
              (slp_gradient_wirtinger_partial Du)" and z=z,
          OF tau_positive exponent_above_two radius_nonnegative
            raw_value_data(1)
            base_target_integrable derivative_target_integrable pointwise_limit
            raw_value_data(2) raw_value_data(4) raw_value_data(3)
            raw_derivative_data(1) raw_value_data(5)
            raw_derivative_data(2)])
qed

end

end
