theory Inverse_Schrodinger_Lp_Center_Kernel_Smooth
  imports Inverse_Schrodinger_Lp_Center_Kernel_Derivative
    Inverse_Schrodinger_Lp_Weak_Product_Wirtinger
begin

section \<open>Smoothness and the classical partial of the center kernel\<close>

lemma slp_center_phase_smooth:
  "smooth_on UNIV (slp_center_phase c)"
proof -
  have coordinate_zero:
    "smooth_on UNIV (\<lambda>z :: slp_point. z $ (0 :: 2))"
    by (rule bounded_linear.smooth_on[OF bounded_linear_vec_nth])
  have coordinate_one:
    "smooth_on UNIV (\<lambda>z :: slp_point. z $ (1 :: 2))"
    by (rule bounded_linear.smooth_on[OF bounded_linear_vec_nth])
  have shifted_zero:
    "smooth_on UNIV
      (\<lambda>z :: slp_point. z $ (0 :: 2) - c $ (0 :: 2))"
    by (rule smooth_on_minus[OF coordinate_zero smooth_on_const open_UNIV])
  have shifted_one:
    "smooth_on UNIV
      (\<lambda>z :: slp_point. z $ (1 :: 2) - c $ (1 :: 2))"
    by (rule smooth_on_minus[OF coordinate_one smooth_on_const open_UNIV])
  have square_zero:
    "smooth_on UNIV
      (\<lambda>z :: slp_point. (z $ (0 :: 2) - c $ (0 :: 2)) ^ 2)"
    using smooth_on_mult[OF shifted_zero shifted_zero open_UNIV]
    by (simp only: power2_eq_square)
  have square_one:
    "smooth_on UNIV
      (\<lambda>z :: slp_point. (z $ (1 :: 2) - c $ (1 :: 2)) ^ 2)"
    using smooth_on_mult[OF shifted_one shifted_one open_UNIV]
    by (simp only: power2_eq_square)
  show ?thesis
    unfolding slp_center_phase_def
    by (rule smooth_on_minus[OF square_zero square_one open_UNIV])
qed

lemma slp_center_kernel_smooth:
  "smooth_on UNIV (slp_center_kernel tau c)"
proof -
  let ?t = "\<lambda>z. tau * slp_center_phase c z"
  have t_smooth: "smooth_on UNIV ?t"
    by (rule smooth_on_mult[OF smooth_on_const
          slp_center_phase_smooth open_UNIV])
  have cos_smooth: "smooth_on UNIV (\<lambda>z. cos (?t z))"
    by (rule smooth_on_cos[OF t_smooth open_UNIV])
  have sin_smooth: "smooth_on UNIV (\<lambda>z. sin (?t z))"
    by (rule smooth_on_sin[OF t_smooth open_UNIV])
  have complex_cos_smooth:
    "smooth_on UNIV (\<lambda>z. of_real (cos (?t z)))"
    unfolding of_real_def
    by (rule smooth_on_scaleR[OF cos_smooth smooth_on_const open_UNIV])
  have complex_sin_smooth:
    "smooth_on UNIV (\<lambda>z. of_real (sin (?t z)))"
    unfolding of_real_def
    by (rule smooth_on_scaleR[OF sin_smooth smooth_on_const open_UNIV])
  have imaginary_sin_smooth:
    "smooth_on UNIV (\<lambda>z. \<i> * of_real (sin (?t z)))"
    by (rule smooth_on_mult[OF smooth_on_const complex_sin_smooth
          open_UNIV])
  have euler_smooth:
    "smooth_on UNIV
      (\<lambda>z. of_real (cos (?t z)) + \<i> * of_real (sin (?t z)))"
    by (rule smooth_on_add[OF complex_cos_smooth imaginary_sin_smooth
          open_UNIV])
  have kernel_eq:
    "slp_center_kernel tau c =
      (\<lambda>z. of_real (cos (?t z)) + \<i> * of_real (sin (?t z)))"
    by (rule ext)
      (simp only: slp_center_kernel_def exp_Euler cos_of_real sin_of_real)
  show ?thesis
    unfolding kernel_eq
    by (rule euler_smooth)
qed

lemma slp_classical_wirtinger_partial_center_kernel:
  "slp_classical_wirtinger_partial (slp_center_kernel tau c) z =
    slp_center_kernel_partial tau c z"
proof -
  have frechet_eq:
    "frechet_derivative (slp_center_kernel tau c) (at z) =
      slp_center_kernel_derivative tau c z"
    by (rule sym, rule frechet_derivative_at[OF
          slp_center_kernel_has_derivative])
  have projection:
    "(D (axis (0 :: 2) 1) - \<i> * D (axis (1 :: 2) 1)) / 2 =
      slp_complex_wirtinger_partial D" for D
  proof -
    have split:
      "(D (axis (0 :: 2) 1) - \<i> * D (axis (1 :: 2) 1)) / 2 =
        D (axis (0 :: 2) 1) / 2 -
          (\<i> * D (axis (1 :: 2) 1)) / 2"
      by (rule diff_divide_distrib)
    show ?thesis
      unfolding slp_complex_wirtinger_partial_def
      by (rule split)
  qed
  show ?thesis
    unfolding slp_classical_wirtinger_partial_def
      slp_complex_partial_derivative_def
      slp_center_kernel_partial_def
      frechet_eq
    by (rule projection)
qed

lemma slp_classical_wirtinger_partial_center_kernel_eq:
  "slp_classical_wirtinger_partial (slp_center_kernel tau c) z =
    \<i> * of_real tau * slp_point_as_complex (z - c) *
      slp_center_kernel tau c z"
  unfolding slp_classical_wirtinger_partial_center_kernel
  by (rule slp_center_kernel_partial_eq)

end
