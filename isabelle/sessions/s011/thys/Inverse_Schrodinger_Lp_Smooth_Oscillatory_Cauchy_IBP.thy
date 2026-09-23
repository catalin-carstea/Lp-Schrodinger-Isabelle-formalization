theory Inverse_Schrodinger_Lp_Smooth_Oscillatory_Cauchy_IBP
  imports
    Inverse_Schrodinger_Lp_Cauchy_Test_Left_Inverse
    Inverse_Schrodinger_Lp_Center_Kernel_Smooth
begin

section \<open>Smooth oscillatory Cauchy integration by parts\<close>

lemma slp_classical_wirtinger_partial_mult:
  assumes a_smooth: "smooth_on UNIV a"
    and phi_smooth: "smooth_on UNIV phi"
  shows "slp_classical_wirtinger_partial (\<lambda>x. a x * phi x) z =
    a z * slp_classical_wirtinger_partial phi z +
      slp_classical_wirtinger_partial a z * phi z"
proof -
  have partial_zero:
    "slp_complex_partial_derivative (\<lambda>x. a x * phi x) 0 z =
      a z * slp_complex_partial_derivative phi 0 z +
        slp_complex_partial_derivative a 0 z * phi z"
    by (rule slp_complex_partial_derivative_mult[OF a_smooth phi_smooth])
  have partial_one:
    "slp_complex_partial_derivative (\<lambda>x. a x * phi x) 1 z =
      a z * slp_complex_partial_derivative phi 1 z +
        slp_complex_partial_derivative a 1 z * phi z"
    by (rule slp_complex_partial_derivative_mult[OF a_smooth phi_smooth])
  have product_algebra:
    "((a z * slp_complex_partial_derivative phi 0 z +
        phi z * slp_complex_partial_derivative a 0 z) -
      \<i> * (a z * slp_complex_partial_derivative phi 1 z +
        phi z * slp_complex_partial_derivative a 1 z)) / 2 =
      a z * ((slp_complex_partial_derivative phi 0 z -
        \<i> * slp_complex_partial_derivative phi 1 z) / 2) +
      phi z * ((slp_complex_partial_derivative a 0 z -
        \<i> * slp_complex_partial_derivative a 1 z) / 2)"
    by (rule slp_wirtinger_product_algebra)
  show ?thesis
    unfolding slp_classical_wirtinger_partial_def
    unfolding partial_zero partial_one
    using product_algebra by (simp only: mult.commute)
qed

context aim_planar_cauchy_test_left_inverse
begin

theorem slp_partial_inverse_oscillatory_product_derivative:
  assumes phi_test: "slp_test_function_on UNIV phi"
  shows "slp_partial_inverse
      (\<lambda>x. slp_center_kernel tau c x *
          slp_classical_wirtinger_partial phi x +
        (\<i> * of_real tau * slp_point_as_complex (x - c) *
          slp_center_kernel tau c x) * phi x) =
    (\<lambda>x. slp_center_kernel tau c x * phi x)"
proof -
  have phi_smooth: "smooth_on UNIV phi"
    using phi_test unfolding slp_test_function_on_def by blast
  have product_test:
    "slp_test_function_on UNIV
      (\<lambda>x. slp_center_kernel tau c x * phi x)"
    by (rule slp_test_function_on_mult_left[OF
          slp_center_kernel_smooth phi_test])
  have left_inverse:
    "slp_partial_inverse
        (slp_classical_wirtinger_partial
          (\<lambda>x. slp_center_kernel tau c x * phi x)) =
      (\<lambda>x. slp_center_kernel tau c x * phi x)"
    by (rule slp_partial_inverse_classical_partial_left_inverse[OF
          product_test])
  have derivative_eq:
    "slp_classical_wirtinger_partial
        (\<lambda>x. slp_center_kernel tau c x * phi x) =
      (\<lambda>x. slp_center_kernel tau c x *
          slp_classical_wirtinger_partial phi x +
        (\<i> * of_real tau * slp_point_as_complex (x - c) *
          slp_center_kernel tau c x) * phi x)"
  proof (rule ext)
    fix x :: slp_point
    show "slp_classical_wirtinger_partial
        (\<lambda>x. slp_center_kernel tau c x * phi x) x =
      slp_center_kernel tau c x *
          slp_classical_wirtinger_partial phi x +
        (\<i> * of_real tau * slp_point_as_complex (x - c) *
          slp_center_kernel tau c x) * phi x"
      unfolding slp_classical_wirtinger_partial_mult[
          OF slp_center_kernel_smooth phi_smooth]
        slp_classical_wirtinger_partial_center_kernel_eq
      by (rule refl)
  qed
  show ?thesis
    using left_inverse unfolding derivative_eq .
qed

end

end
