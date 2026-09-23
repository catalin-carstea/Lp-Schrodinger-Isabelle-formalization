theory Inverse_Schrodinger_Lp_Fourier_Damped_Chirp_Product
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Fourier_Damped_Center_Kernel"
begin

section \<open>Coordinate separation of the damped center chirp\<close>

definition slp_damped_chirp_1 ::
  "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> complex"
where
  "slp_damped_chirp_1 eps tau x =
    slp_scaled_gaussian (2 * eps) x *
      exp (\<i> * of_real (tau * x ^ 2))"

lemma slp_damped_chirp_1_factor:
  "slp_damped_chirp_1 eps tau x =
    of_real (exp (- eps * x ^ 2)) *
      exp (\<i> * of_real (tau * x ^ 2))"
proof -
  have exponent: "- (2 * eps) * x ^ 2 / 2 = - eps * x ^ 2"
    by (simp add: algebra_simps)
  show ?thesis
    unfolding slp_damped_chirp_1_def slp_scaled_gaussian_def
    by (simp only: exponent)
qed

lemma slp_damped_chirp_1_measurable[measurable]:
  "slp_damped_chirp_1 eps tau \<in> borel_measurable lborel"
  unfolding slp_damped_chirp_1_def slp_scaled_gaussian_def
  by measurable

lemma slp_damped_chirp_1_norm [simp]:
  "cmod (slp_damped_chirp_1 eps tau x) = exp (- eps * x ^ 2)"
  unfolding slp_damped_chirp_1_factor
  by (simp only: norm_mult norm_of_real abs_of_pos exp_gt_zero
      norm_exp_i_times mult_1_right)

lemma slp_damped_chirp_1_integrable:
  assumes eps: "0 < eps"
  shows "integrable lborel (slp_damped_chirp_1 eps tau)"
proof (rule Bochner_Integration.integrable_bound[
    OF slp_scaled_gaussian_integrable])
  show "0 < 2 * eps"
    using eps by simp
  show "slp_damped_chirp_1 eps tau \<in> borel_measurable lborel"
    by measurable
  show "AE x in lborel.
      norm_class.norm (slp_damped_chirp_1 eps tau x) \<le>
      norm_class.norm (slp_scaled_gaussian (2 * eps) x)"
    unfolding slp_damped_chirp_1_def
    by (simp only: norm_mult norm_exp_i_times mult_1_right order_refl
        eventually_True)
qed

lemma slp_damped_center_kernel_coordinate_product:
  "slp_damped_center_kernel eps tau x =
    slp_damped_chirp_1 eps tau (x $ (0 :: 2)) *
      slp_damped_chirp_1 eps (- tau) (x $ (1 :: 2))"
proof -
  have universe_two: "(UNIV :: 2 set) = {0, 1}"
    using UNIV_2 by auto
  have gaussian:
      "slp_planar_radial_gaussian (2 * eps) x =
        slp_scaled_gaussian (2 * eps) (x $ (0 :: 2)) *
          slp_scaled_gaussian (2 * eps) (x $ (1 :: 2))"
    unfolding slp_planar_radial_gaussian_product
      slp_planar_scaled_gaussian_def universe_two
    by simp
  have exponent:
      "\<i> * of_real
          (tau * ((x $ (0 :: 2)) ^ 2 - (x $ (1 :: 2)) ^ 2)) =
        \<i> * of_real (tau * (x $ (0 :: 2)) ^ 2) +
          \<i> * of_real ((- tau) * (x $ (1 :: 2)) ^ 2)"
    by (simp add: algebra_simps)
  have chirp:
      "slp_center_kernel tau 0 x =
        exp (\<i> * of_real (tau * (x $ (0 :: 2)) ^ 2)) *
          exp (\<i> * of_real ((- tau) * (x $ (1 :: 2)) ^ 2))"
    unfolding slp_center_kernel_def slp_center_phase_def zero_vec_def
    by (simp only: vec_lambda_beta diff_zero exponent exp_add)
  show ?thesis
    unfolding slp_damped_center_kernel_def slp_damped_chirp_1_def
      gaussian chirp
    by (simp only: mult_ac)
qed

lemma slp_damped_center_fourier_integrand_coordinate_product:
  "slp_fourier_phase xi x * slp_damped_center_kernel eps tau x =
    (exp (\<i> * of_real (- (xi $ (0 :: 2)) * (x $ (0 :: 2)))) *
      slp_damped_chirp_1 eps tau (x $ (0 :: 2))) *
    (exp (\<i> * of_real (- (xi $ (1 :: 2)) * (x $ (1 :: 2)))) *
      slp_damped_chirp_1 eps (- tau) (x $ (1 :: 2)))"
proof -
  have universe_two: "(UNIV :: 2 set) = {0, 1}"
    using UNIV_2 by auto
  have exponent:
      "\<i> * of_real (- inner x xi) =
        \<i> * of_real (- (xi $ (0 :: 2)) * (x $ (0 :: 2))) +
          \<i> * of_real (- (xi $ (1 :: 2)) * (x $ (1 :: 2)))"
  proof -
    have coordinate_zero:
        "(x $ (0 :: 2)) * (xi $ (0 :: 2)) =
          (xi $ (0 :: 2)) * (x $ (0 :: 2))"
      by (rule mult.commute)
    have coordinate_one:
        "(x $ (1 :: 2)) * (xi $ (1 :: 2)) =
          (xi $ (1 :: 2)) * (x $ (1 :: 2))"
      by (rule mult.commute)
    have inner_two:
        "inner x xi =
          (xi $ (0 :: 2)) * (x $ (0 :: 2)) +
            (xi $ (1 :: 2)) * (x $ (1 :: 2))"
      unfolding inner_vec_def universe_two
      by (simp add: coordinate_zero coordinate_one)
    have scalar:
        "- inner x xi =
          (- (xi $ (0 :: 2))) * (x $ (0 :: 2)) +
            (- (xi $ (1 :: 2))) * (x $ (1 :: 2))"
      unfolding inner_two
      by (simp only: minus_add_distrib minus_mult_left)
    show ?thesis
      unfolding scalar
      by (simp only: of_real_add distrib_left)
  qed
  have phase:
      "slp_fourier_phase xi x =
        exp (\<i> * of_real (- (xi $ (0 :: 2)) * (x $ (0 :: 2)))) *
          exp (\<i> * of_real (- (xi $ (1 :: 2)) * (x $ (1 :: 2))))"
    unfolding slp_fourier_phase_def exponent
    by (rule exp_add)
  show ?thesis
    unfolding phase slp_damped_center_kernel_coordinate_product
    by (simp only: mult_ac)
qed

end
