theory Inverse_Schrodinger_Lp_Fourier_Standard_Gaussian
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Fourier_Covariance"
    "HOL-Probability.Characteristic_Functions"
begin

section \<open>Standard one-dimensional Gaussian Fourier integral\<close>

definition slp_standard_gaussian :: "real \<Rightarrow> complex" where
  "slp_standard_gaussian x =
    of_real (sqrt (2 * pi) * normal_density 0 1 x)"

lemma slp_standard_gaussian_explicit:
  "slp_standard_gaussian x = of_real (exp (- (x ^ 2) / 2))"
proof -
  have sqrt_positive: "0 < sqrt (pi * 2)"
    by (rule real_sqrt_gt_zero) (simp add: pi_gt_zero)
  have sqrt_nonzero: "sqrt (pi * 2) \<noteq> 0"
    using sqrt_positive by simp
  show ?thesis
    unfolding slp_standard_gaussian_def std_normal_density_def
    by (simp add: sqrt_nonzero mult_ac)
qed

lemma slp_standard_gaussian_measurable[measurable]:
  "slp_standard_gaussian \<in> borel_measurable lborel"
  unfolding slp_standard_gaussian_def by measurable

lemma slp_standard_gaussian_integrable:
  "integrable lborel slp_standard_gaussian"
  unfolding slp_standard_gaussian_def of_real_mult
  by (intro Bochner_Integration.integrable_mult_right integrable_of_real)
    simp

lemma slp_standard_gaussian_integral:
  "integral\<^sup>L lborel slp_standard_gaussian = of_real (sqrt (2 * pi))"
  unfolding slp_standard_gaussian_def of_real_mult
  by (simp add: Bochner_Integration.integral_mult_right)

lemma slp_standard_gaussian_fourier_integrable:
  "integrable lborel
    (\<lambda>x. exp (\<i> * of_real (- xi * x)) * slp_standard_gaussian x)"
proof (rule Bochner_Integration.integrable_bound[
    OF slp_standard_gaussian_integrable])
  show "(\<lambda>x. exp (\<i> * of_real (- xi * x)) *
      slp_standard_gaussian x) \<in> borel_measurable lborel"
    by measurable
  show "AE x in lborel.
      norm_class.norm
          (exp (\<i> * of_real (- xi * x)) * slp_standard_gaussian x)
        \<le> norm_class.norm (slp_standard_gaussian x)"
    by (rule AE_I2)
      (simp only: norm_mult norm_exp_i_times mult.left_neutral order_refl)
qed

lemma slp_standard_gaussian_fourier_integral:
  "integral\<^sup>L lborel
      (\<lambda>x. exp (\<i> * of_real (- xi * x)) * slp_standard_gaussian x) =
    of_real (sqrt (2 * pi) * exp (- (xi ^ 2) / 2))"
proof -
  have characteristic:
      "char std_normal_distribution (-xi) =
        of_real (exp (- (xi ^ 2) / 2))"
    using fun_cong[OF char_std_normal_distribution, of "-xi"] by simp
  have density_integral:
      "integral\<^sup>L lborel
          (\<lambda>x. normal_density 0 1 x *\<^sub>R
            exp (\<i> * of_real (- xi * x))) =
        of_real (exp (- (xi ^ 2) / 2))"
  proof -
    have phase_measurable:
        "(\<lambda>x. iexp ((-xi) * x)) \<in> borel_measurable lborel"
      by measurable
    have
        "char std_normal_distribution (-xi) =
          integral\<^sup>L lborel
            (\<lambda>x. normal_density 0 1 x *\<^sub>R iexp ((-xi) * x))"
      unfolding char_def
      by (rule integral_density)
        (use phase_measurable in simp_all)
    then show ?thesis
      using characteristic by simp
  qed
  have integrand_identity:
      "(\<lambda>x. exp (\<i> * of_real (- xi * x)) *
          slp_standard_gaussian x) =
        (\<lambda>x. of_real (sqrt (2 * pi)) *
          (normal_density 0 1 x *\<^sub>R
            exp (\<i> * of_real (- xi * x))))"
    by (rule ext)
      (simp add: slp_standard_gaussian_def scaleR_conv_of_real algebra_simps)
  have base_integrable:
      "integrable lborel
        (\<lambda>x. normal_density 0 1 x *\<^sub>R
          exp (\<i> * of_real (- xi * x)))"
  proof -
    have normal_complex_integrable:
        "integrable lborel
          (\<lambda>x. (of_real (normal_density 0 1 x) :: complex))"
      by (rule integrable_of_real) simp
    show ?thesis
    proof (rule Bochner_Integration.integrable_bound[
        OF normal_complex_integrable])
    show "(\<lambda>x. normal_density 0 1 x *\<^sub>R
        exp (\<i> * of_real (- xi * x))) \<in> borel_measurable lborel"
      by measurable
    show "AE x in lborel.
        norm_class.norm
            (normal_density 0 1 x *\<^sub>R
              exp (\<i> * of_real (- xi * x)))
          \<le> norm_class.norm
            (of_real (normal_density 0 1 x) :: complex)"
      by (rule AE_I2)
        (simp only: scaleR_conv_of_real norm_mult norm_exp_i_times
          mult.right_neutral norm_of_real order_refl)
    qed
  qed
  show ?thesis
    unfolding integrand_identity
    apply (subst Bochner_Integration.integral_mult_right[OF base_integrable])
    using density_integral
    by (simp add: of_real_mult)
qed

end
