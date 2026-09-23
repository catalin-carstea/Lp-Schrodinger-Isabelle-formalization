theory Inverse_Schrodinger_Lp_Oscillatory_Cauchy_Division
  imports Inverse_Schrodinger_Lp_Cauchy_Scalar_Extraction
begin

section \<open>Positive-parameter division in the smooth oscillatory identity\<close>

context aim_planar_cauchy_test_left_inverse
begin

corollary slp_partial_inverse_oscillatory_divided:
  assumes tau_pos: "0 < tau"
    and phi_test: "slp_test_function_on UNIV phi"
  shows "slp_partial_inverse
      (\<lambda>x. (slp_point_as_complex (x - c) *
        slp_center_kernel tau c x) * phi x) z =
    (1 / (\<i> * of_real tau)) *
      (slp_center_kernel tau c z * phi z -
        slp_partial_inverse
          (\<lambda>x. slp_center_kernel tau c x *
            slp_classical_wirtinger_partial phi x) z)"
proof -
  have tau_nonzero: "tau \<noteq> 0"
    using tau_pos by linarith
  have scalar_nonzero: "(\<i> * of_real tau :: complex) \<noteq> 0"
    by (simp add: tau_nonzero)
  let ?a = "\<i> * of_real tau"
  let ?X = "slp_partial_inverse
    (\<lambda>x. (slp_point_as_complex (x - c) *
      slp_center_kernel tau c x) * phi x) z"
  let ?B = "slp_center_kernel tau c z * phi z -
    slp_partial_inverse
      (\<lambda>x. slp_center_kernel tau c x *
        slp_classical_wirtinger_partial phi x) z"
  have extracted: "?a * ?X = ?B"
    by (rule slp_partial_inverse_oscillatory_scalar_extracted[OF phi_test])
  have scaled: "inverse ?a * (?a * ?X) = inverse ?a * ?B"
    by (rule arg_cong[OF extracted])
  have inverse_product: "inverse ?a * ?a = 1"
    by (rule left_inverse[OF scalar_nonzero])
  have reassociated:
      "inverse ?a * (?a * ?X) = (inverse ?a * ?a) * ?X"
    by (rule sym[OF mult.assoc])
  have product_replaced: "(inverse ?a * ?a) * ?X = 1 * ?X"
    by (rule arg_cong[OF inverse_product])
  have neutral: "1 * ?X = ?X"
    by (rule mult_1_left)
  have cancel_left: "inverse ?a * (?a * ?X) = ?X"
    by (rule trans[OF reassociated trans[OF product_replaced neutral]])
  have cancelled: "?X = inverse ?a * ?B"
    by (rule trans[OF sym[OF cancel_left] scaled])
  show ?thesis
    using cancelled by (simp only: divide_inverse mult_1_left)
qed

end

end
