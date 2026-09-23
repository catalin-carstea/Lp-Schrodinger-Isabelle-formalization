theory Inverse_Schrodinger_Lp_Fourier_Damped_Center_Kernel
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Fourier_Radial_Gaussian"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Center_Average_Physical"
begin

section \<open>Gaussian damping of the zero-center quadratic chirp\<close>

definition slp_damped_center_kernel ::
  "real \<Rightarrow> real \<Rightarrow> slp_point \<Rightarrow> complex"
where
  "slp_damped_center_kernel eps tau x =
    slp_planar_radial_gaussian (2 * eps) x *
      slp_center_kernel tau 0 x"

lemma slp_damped_center_kernel_factor:
  "slp_damped_center_kernel eps tau x =
    of_real
      (exp (- eps * (Real_Vector_Spaces.norm x) ^ 2)) *
    exp (\<i> * of_real
      (tau * ((x $ (0 :: 2)) ^ 2 - (x $ (1 :: 2)) ^ 2)))"
proof -
  have exponent:
      "- (2 * eps) * (Real_Vector_Spaces.norm x) ^ 2 / 2 =
        - eps * (Real_Vector_Spaces.norm x) ^ 2"
    by (simp add: algebra_simps)
  show ?thesis
    unfolding slp_damped_center_kernel_def
      slp_planar_radial_gaussian_def
      slp_center_kernel_def slp_center_phase_def
    by (simp only: exponent zero_vec_def vec_lambda_beta diff_zero)
qed

lemma slp_damped_center_kernel_measurable[measurable]:
  "slp_damped_center_kernel eps tau \<in> borel_measurable lborel"
  unfolding slp_damped_center_kernel_def
    slp_planar_radial_gaussian_def
    slp_center_kernel_def slp_center_phase_def
  by measurable

lemma slp_damped_center_kernel_norm [simp]:
  "cmod (slp_damped_center_kernel eps tau x) =
    exp (- eps * (Real_Vector_Spaces.norm x) ^ 2)"
  unfolding slp_damped_center_kernel_factor
  by (simp only: norm_mult norm_of_real abs_of_pos exp_gt_zero
      norm_exp_i_times mult_1_right)

lemma slp_damped_center_kernel_integrable:
  assumes eps: "0 < eps"
  shows "integrable lborel (slp_damped_center_kernel eps tau)"
proof (rule Bochner_Integration.integrable_bound[
    OF slp_planar_radial_gaussian_integrable])
  show "0 < 2 * eps"
    using eps by simp
  show "slp_damped_center_kernel eps tau \<in>
      borel_measurable lborel"
    by measurable
  show "AE x in lborel.
      Real_Vector_Spaces.norm
        (slp_damped_center_kernel eps tau x) \<le>
      Real_Vector_Spaces.norm
        (slp_planar_radial_gaussian (2 * eps) x)"
    unfolding slp_damped_center_kernel_def slp_center_kernel_def
    by (simp only: norm_mult norm_exp_i_times mult_1_right
        order_refl eventually_True)
qed

end
