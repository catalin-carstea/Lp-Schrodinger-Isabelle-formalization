theory Inverse_Schrodinger_Lp_Oscillatory_Test_Closure
  imports
    Inverse_Schrodinger_Lp_Cauchy_Test_Integrable
    Inverse_Schrodinger_Lp_Smooth_Oscillatory_Cauchy_IBP
begin

section \<open>Test-function closure for the smooth oscillatory split\<close>

lemma slp_test_function_on_add:
  assumes f_test: "slp_test_function_on U f"
    and g_test: "slp_test_function_on U g"
  shows "slp_test_function_on U (\<lambda>x. f x + g x)"
proof -
  have f_smooth: "smooth_on UNIV f"
    using f_test unfolding slp_test_function_on_def by blast
  have g_smooth: "smooth_on UNIV g"
    using g_test unfolding slp_test_function_on_def by blast
  have f_compact: "compact (closure {x. f x \<noteq> 0})"
    using f_test unfolding slp_test_function_on_def by blast
  have g_compact: "compact (closure {x. g x \<noteq> 0})"
    using g_test unfolding slp_test_function_on_def by blast
  have f_within: "closure {x. f x \<noteq> 0} \<subseteq> U"
    using f_test unfolding slp_test_function_on_def by blast
  have g_within: "closure {x. g x \<noteq> 0} \<subseteq> U"
    using g_test unfolding slp_test_function_on_def by blast
  have sum_smooth: "smooth_on UNIV (\<lambda>x. f x + g x)"
    by (rule smooth_on_add[OF f_smooth g_smooth open_UNIV])
  have nonzero_subset:
      "{x. f x + g x \<noteq> 0} \<subseteq>
        {x. f x \<noteq> 0} \<union> {x. g x \<noteq> 0}"
    by auto
  have sum_support_subset:
      "closure {x. f x + g x \<noteq> 0} \<subseteq>
        closure {x. f x \<noteq> 0} \<union> closure {x. g x \<noteq> 0}"
  proof -
    have "closure {x. f x + g x \<noteq> 0} \<subseteq>
        closure ({x. f x \<noteq> 0} \<union> {x. g x \<noteq> 0})"
      by (rule closure_mono[OF nonzero_subset])
    then show ?thesis by simp
  qed
  have sum_compact: "compact (closure {x. f x + g x \<noteq> 0})"
    by (rule compact_if_closed_subset_of_compact[OF closed_closure
          compact_Un[OF f_compact g_compact] sum_support_subset])
  have sum_within: "closure {x. f x + g x \<noteq> 0} \<subseteq> U"
    using sum_support_subset f_within g_within by blast
  show ?thesis
    unfolding slp_test_function_on_def
    by (rule conjI[OF sum_smooth conjI[OF sum_compact sum_within]])
qed

lemma slp_classical_wirtinger_partial_test_function:
  assumes phi_test: "slp_test_function_on U phi"
  shows "slp_test_function_on U (slp_classical_wirtinger_partial phi)"
proof -
  have derivative_zero:
      "slp_test_function_on U (slp_complex_partial_derivative phi 0)"
    by (rule slp_test_function_on_partial_derivative[OF phi_test])
  have derivative_one:
      "slp_test_function_on U (slp_complex_partial_derivative phi 1)"
    by (rule slp_test_function_on_partial_derivative[OF phi_test])
  have imaginary_derivative:
      "slp_test_function_on U
        (\<lambda>x. (- \<i>) * slp_complex_partial_derivative phi 1 x)"
    by (rule slp_test_function_on_mult_left[OF smooth_on_const derivative_one])
  have derivative_sum:
      "slp_test_function_on U
        (\<lambda>x. slp_complex_partial_derivative phi 0 x +
          (- \<i>) * slp_complex_partial_derivative phi 1 x)"
    by (rule slp_test_function_on_add[OF derivative_zero
          imaginary_derivative])
  have scaled_sum:
      "slp_test_function_on U
        (\<lambda>x. inverse (2 :: complex) *
          (slp_complex_partial_derivative phi 0 x +
            (- \<i>) * slp_complex_partial_derivative phi 1 x))"
    by (rule slp_test_function_on_mult_left[OF smooth_on_const derivative_sum])
  have scaled_eq:
      "(\<lambda>x. inverse (2 :: complex) *
          (slp_complex_partial_derivative phi 0 x +
            (- \<i>) * slp_complex_partial_derivative phi 1 x)) =
        slp_classical_wirtinger_partial phi"
  proof (rule ext)
    fix x
    show "inverse (2 :: complex) *
          (slp_complex_partial_derivative phi 0 x +
            (- \<i>) * slp_complex_partial_derivative phi 1 x) =
        slp_classical_wirtinger_partial phi x"
      by (simp only: slp_classical_wirtinger_partial_def
            divide_inverse mult_minus_left add_uminus_conv_diff mult.commute)
  qed
  show ?thesis
    using scaled_sum unfolding scaled_eq .
qed

lemma slp_point_as_complex_smooth:
  "smooth_on UNIV slp_point_as_complex"
proof -
  have coordinate_zero:
      "smooth_on UNIV (\<lambda>z :: slp_point. z $ (0 :: 2))"
    by (rule bounded_linear.smooth_on[OF bounded_linear_vec_nth])
  have coordinate_one:
      "smooth_on UNIV (\<lambda>z :: slp_point. z $ (1 :: 2))"
    by (rule bounded_linear.smooth_on[OF bounded_linear_vec_nth])
  have real_zero:
      "smooth_on UNIV (\<lambda>z :: slp_point. of_real (z $ (0 :: 2)))"
    unfolding of_real_def
    by (rule smooth_on_scaleR[OF coordinate_zero smooth_on_const open_UNIV])
  have real_one:
      "smooth_on UNIV (\<lambda>z :: slp_point. of_real (z $ (1 :: 2)))"
    unfolding of_real_def
    by (rule smooth_on_scaleR[OF coordinate_one smooth_on_const open_UNIV])
  have imaginary_one:
      "smooth_on UNIV
        (\<lambda>z :: slp_point. \<i> * of_real (z $ (1 :: 2)))"
    by (rule smooth_on_mult[OF smooth_on_const real_one open_UNIV])
  have coordinate_sum:
      "smooth_on UNIV
        (\<lambda>z :: slp_point.
          of_real (z $ (0 :: 2)) + \<i> * of_real (z $ (1 :: 2)))"
    by (rule smooth_on_add[OF real_zero imaginary_one open_UNIV])
  show ?thesis
    unfolding slp_point_as_complex_def Complex_eq
    by (rule coordinate_sum)
qed

lemma slp_shifted_point_as_complex_smooth:
  "smooth_on UNIV (\<lambda>x. slp_point_as_complex (x - c))"
proof -
  have shift_smooth: "smooth_on UNIV (\<lambda>x :: slp_point. x - c)"
    by (rule smooth_on_minus[OF smooth_on_id smooth_on_const open_UNIV])
  have composed_smooth: "smooth_on UNIV
      (slp_point_as_complex \<circ> (\<lambda>x :: slp_point. x - c))"
    by (rule smooth_on_compose[OF slp_point_as_complex_smooth shift_smooth])
      auto
  have composed_eq:
      "(slp_point_as_complex \<circ> (\<lambda>x :: slp_point. x - c)) =
        (\<lambda>x. slp_point_as_complex (x - c))"
    by (rule ext) (simp only: o_apply)
  show ?thesis
    using composed_smooth unfolding composed_eq .
qed

lemma slp_center_partial_coefficient_smooth:
  "smooth_on UNIV
    (\<lambda>x. \<i> * of_real tau * slp_point_as_complex (x - c) *
      slp_center_kernel tau c x)"
proof -
  have linear_smooth:
      "smooth_on UNIV
        (\<lambda>x. \<i> * of_real tau * slp_point_as_complex (x - c))"
    by (rule smooth_on_mult[OF smooth_on_const
          slp_shifted_point_as_complex_smooth open_UNIV])
  show ?thesis
    by (rule smooth_on_mult[OF linear_smooth slp_center_kernel_smooth
          open_UNIV])
qed

lemma slp_oscillatory_derivative_summands_test_function:
  assumes phi_test: "slp_test_function_on UNIV phi"
  shows "slp_test_function_on UNIV
      (\<lambda>x. slp_center_kernel tau c x *
        slp_classical_wirtinger_partial phi x)"
    and "slp_test_function_on UNIV
      (\<lambda>x. (\<i> * of_real tau * slp_point_as_complex (x - c) *
        slp_center_kernel tau c x) * phi x)"
proof -
  show "slp_test_function_on UNIV
      (\<lambda>x. slp_center_kernel tau c x *
        slp_classical_wirtinger_partial phi x)"
    by (rule slp_test_function_on_mult_left[OF slp_center_kernel_smooth
          slp_classical_wirtinger_partial_test_function[OF phi_test]])
  show "slp_test_function_on UNIV
      (\<lambda>x. (\<i> * of_real tau * slp_point_as_complex (x - c) *
        slp_center_kernel tau c x) * phi x)"
    by (rule slp_test_function_on_mult_left[OF
          slp_center_partial_coefficient_smooth phi_test])
qed

end
