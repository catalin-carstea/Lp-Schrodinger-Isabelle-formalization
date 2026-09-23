theory Inverse_Schrodinger_Lp_Cauchy_Scalar_Extraction
  imports Inverse_Schrodinger_Lp_Smooth_Oscillatory_Cauchy_Split
begin

section \<open>Guarded complex-scalar linearity of the Cauchy transform\<close>

lemma slp_cauchy_integrable_at_mult_left:
  assumes f_integrable: "slp_cauchy_integrable_at orientation f z"
  shows "slp_cauchy_integrable_at orientation (\<lambda>y. a * f y) z"
proof -
  have f_int: "integrable lborel (slp_cauchy_integrand orientation f z)"
    using f_integrable unfolding slp_cauchy_integrable_at_def .
  have integrand_mult:
      "slp_cauchy_integrand orientation (\<lambda>y. a * f y) z =
        (\<lambda>y. a * slp_cauchy_integrand orientation f z y)"
    by (rule ext) (simp only: slp_cauchy_integrand_def mult.assoc)
  show ?thesis
    unfolding slp_cauchy_integrable_at_def integrand_mult
    by (rule Bochner_Integration.integrable_mult_right) (rule f_int)
qed

lemma slp_cauchy_transform_mult_left:
  assumes f_integrable: "slp_cauchy_integrable_at orientation f z"
  shows "slp_cauchy_transform orientation (\<lambda>y. a * f y) z =
    a * slp_cauchy_transform orientation f z"
proof -
  have f_int: "integrable lborel (slp_cauchy_integrand orientation f z)"
    using f_integrable unfolding slp_cauchy_integrable_at_def .
  have integrand_mult:
      "slp_cauchy_integrand orientation (\<lambda>y. a * f y) z =
        (\<lambda>y. a * slp_cauchy_integrand orientation f z y)"
    by (rule ext) (simp only: slp_cauchy_integrand_def mult.assoc)
  have integral_mult_eq:
      "integral\<^sup>L lborel
          (slp_cauchy_integrand orientation (\<lambda>y. a * f y) z) =
        a * integral\<^sup>L lborel (slp_cauchy_integrand orientation f z)"
    unfolding integrand_mult
    by (rule Bochner_Integration.integral_mult_right) (rule f_int)
  show ?thesis
    unfolding slp_cauchy_transform_def integral_mult_eq
    by (simp add: algebra_simps)
qed

lemma slp_center_coordinate_amplitude_test_function:
  assumes phi_test: "slp_test_function_on UNIV phi"
  shows "slp_test_function_on UNIV
    (\<lambda>x. (slp_point_as_complex (x - c) *
      slp_center_kernel tau c x) * phi x)"
proof -
  have coefficient_smooth: "smooth_on UNIV
      (\<lambda>x. slp_point_as_complex (x - c) *
        slp_center_kernel tau c x)"
    by (rule smooth_on_mult[OF slp_shifted_point_as_complex_smooth
          slp_center_kernel_smooth open_UNIV])
  show ?thesis
    by (rule slp_test_function_on_mult_left[OF coefficient_smooth phi_test])
qed

context aim_planar_cauchy_test_left_inverse
begin

theorem slp_partial_inverse_oscillatory_scalar_extracted:
  assumes phi_test: "slp_test_function_on UNIV phi"
  shows "(\<i> * of_real tau) *
      slp_partial_inverse
        (\<lambda>x. (slp_point_as_complex (x - c) *
          slp_center_kernel tau c x) * phi x) z =
    slp_center_kernel tau c z * phi z -
      slp_partial_inverse
        (\<lambda>x. slp_center_kernel tau c x *
          slp_classical_wirtinger_partial phi x) z"
proof -
  have base_test: "slp_test_function_on UNIV
      (\<lambda>x. (slp_point_as_complex (x - c) *
        slp_center_kernel tau c x) * phi x)"
    by (rule slp_center_coordinate_amplitude_test_function[OF phi_test])
  have base_integrable: "slp_cauchy_integrable_at SLP_Partial_Inverse
      (\<lambda>x. (slp_point_as_complex (x - c) *
        slp_center_kernel tau c x) * phi x) z"
    by (rule slp_test_function_cauchy_integrable_at[OF base_test])
  have input_eq:
      "(\<lambda>x. (\<i> * of_real tau * slp_point_as_complex (x - c) *
          slp_center_kernel tau c x) * phi x) =
        (\<lambda>x. (\<i> * of_real tau) *
          ((slp_point_as_complex (x - c) *
            slp_center_kernel tau c x) * phi x))"
    by (rule ext) (simp only: mult.assoc)
  have scaled_transform:
      "slp_partial_inverse
          (\<lambda>x. (\<i> * of_real tau * slp_point_as_complex (x - c) *
            slp_center_kernel tau c x) * phi x) z =
        (\<i> * of_real tau) *
          slp_partial_inverse
            (\<lambda>x. (slp_point_as_complex (x - c) *
              slp_center_kernel tau c x) * phi x) z"
    unfolding input_eq
    by (rule slp_cauchy_transform_mult_left[OF base_integrable])
  have isolated:
      "slp_partial_inverse
          (\<lambda>x. (\<i> * of_real tau * slp_point_as_complex (x - c) *
            slp_center_kernel tau c x) * phi x) z =
        slp_center_kernel tau c z * phi z -
          slp_partial_inverse
            (\<lambda>x. slp_center_kernel tau c x *
              slp_classical_wirtinger_partial phi x) z"
    by (rule slp_partial_inverse_oscillatory_second_summand[OF phi_test])
  show ?thesis
    by (rule trans[OF sym[OF scaled_transform] isolated])
qed

end

end
