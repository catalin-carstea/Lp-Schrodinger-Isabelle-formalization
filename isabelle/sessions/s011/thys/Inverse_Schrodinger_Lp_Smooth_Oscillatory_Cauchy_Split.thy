theory Inverse_Schrodinger_Lp_Smooth_Oscillatory_Cauchy_Split
  imports Inverse_Schrodinger_Lp_Oscillatory_Test_Closure
begin

section \<open>Guarded splitting of the smooth oscillatory Cauchy identity\<close>

context aim_planar_cauchy_test_left_inverse
begin

theorem slp_partial_inverse_oscillatory_summand_split:
  assumes phi_test: "slp_test_function_on UNIV phi"
  shows "slp_partial_inverse
        (\<lambda>x. slp_center_kernel tau c x *
          slp_classical_wirtinger_partial phi x) z +
      slp_partial_inverse
        (\<lambda>x. (\<i> * of_real tau * slp_point_as_complex (x - c) *
          slp_center_kernel tau c x) * phi x) z =
      slp_center_kernel tau c z * phi z"
proof -
  have first_test: "slp_test_function_on UNIV
      (\<lambda>x. slp_center_kernel tau c x *
        slp_classical_wirtinger_partial phi x)"
    by (rule slp_oscillatory_derivative_summands_test_function(1)[OF
          phi_test])
  have second_test: "slp_test_function_on UNIV
      (\<lambda>x. (\<i> * of_real tau * slp_point_as_complex (x - c) *
        slp_center_kernel tau c x) * phi x)"
    by (rule slp_oscillatory_derivative_summands_test_function(2)[OF
          phi_test])
  have first_integrable: "slp_cauchy_integrable_at SLP_Partial_Inverse
      (\<lambda>x. slp_center_kernel tau c x *
        slp_classical_wirtinger_partial phi x) z"
    by (rule slp_test_function_cauchy_integrable_at[OF first_test])
  have second_integrable: "slp_cauchy_integrable_at SLP_Partial_Inverse
      (\<lambda>x. (\<i> * of_real tau * slp_point_as_complex (x - c) *
        slp_center_kernel tau c x) * phi x) z"
    by (rule slp_test_function_cauchy_integrable_at[OF second_test])
  have transform_split:
      "slp_partial_inverse
          (\<lambda>x. slp_center_kernel tau c x *
              slp_classical_wirtinger_partial phi x +
            (\<i> * of_real tau * slp_point_as_complex (x - c) *
              slp_center_kernel tau c x) * phi x) z =
        slp_partial_inverse
          (\<lambda>x. slp_center_kernel tau c x *
            slp_classical_wirtinger_partial phi x) z +
        slp_partial_inverse
          (\<lambda>x. (\<i> * of_real tau * slp_point_as_complex (x - c) *
            slp_center_kernel tau c x) * phi x) z"
    by (rule slp_cauchy_transform_add[OF first_integrable second_integrable])
  have combined_function:
      "slp_partial_inverse
          (\<lambda>x. slp_center_kernel tau c x *
              slp_classical_wirtinger_partial phi x +
            (\<i> * of_real tau * slp_point_as_complex (x - c) *
              slp_center_kernel tau c x) * phi x) =
        (\<lambda>x. slp_center_kernel tau c x * phi x)"
    by (rule slp_partial_inverse_oscillatory_product_derivative[OF phi_test])
  have combined_at:
      "slp_partial_inverse
          (\<lambda>x. slp_center_kernel tau c x *
              slp_classical_wirtinger_partial phi x +
            (\<i> * of_real tau * slp_point_as_complex (x - c) *
              slp_center_kernel tau c x) * phi x) z =
        slp_center_kernel tau c z * phi z"
    by (rule fun_cong[OF combined_function])
  show ?thesis
    by (rule trans[OF sym[OF transform_split] combined_at])
qed

corollary slp_partial_inverse_oscillatory_second_summand:
  assumes phi_test: "slp_test_function_on UNIV phi"
  shows "slp_partial_inverse
      (\<lambda>x. (\<i> * of_real tau * slp_point_as_complex (x - c) *
        slp_center_kernel tau c x) * phi x) z =
    slp_center_kernel tau c z * phi z -
      slp_partial_inverse
        (\<lambda>x. slp_center_kernel tau c x *
          slp_classical_wirtinger_partial phi x) z"
  using slp_partial_inverse_oscillatory_summand_split[OF phi_test, of tau c z]
  by (simp only: eq_diff_eq add.commute)

end

end
