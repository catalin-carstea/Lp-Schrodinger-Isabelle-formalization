theory Inverse_Schrodinger_Lp_Fourier_Scaled_Gaussian
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Fourier_Standard_Gaussian"
begin

section \<open>Positive real scaling of the standard Gaussian\<close>

definition slp_scaled_gaussian :: "real \<Rightarrow> real \<Rightarrow> complex" where
  "slp_scaled_gaussian a x = of_real (exp (- a * (x ^ 2) / 2))"

lemma slp_scaled_gaussian_pullback:
  assumes a: "0 < a"
  shows "slp_scaled_gaussian a x =
    slp_standard_gaussian (sqrt a * x)"
  unfolding slp_scaled_gaussian_def
  using a
  by (simp add: slp_standard_gaussian_explicit power_mult_distrib)

lemma slp_scaled_gaussian_measurable[measurable]:
  "slp_scaled_gaussian a \<in> borel_measurable lborel"
  unfolding slp_scaled_gaussian_def by measurable

lemma slp_scaled_gaussian_integrable:
  assumes a: "0 < a"
  shows "integrable lborel (slp_scaled_gaussian a)"
proof -
  have sqrt_nonzero: "sqrt a \<noteq> 0"
    using a by simp
  have pulled:
      "integrable lborel
        (\<lambda>x. slp_standard_gaussian (0 + sqrt a * x))"
    by (rule lborel_integrable_real_affine[
        OF slp_standard_gaussian_integrable sqrt_nonzero])
  have function_identity:
      "slp_scaled_gaussian a =
        (\<lambda>x. slp_standard_gaussian (sqrt a * x))"
    by (rule ext)
      (rule slp_scaled_gaussian_pullback[OF a])
  show ?thesis
    using pulled function_identity by simp
qed

lemma slp_scaled_gaussian_fourier_integrable:
  assumes a: "0 < a"
  shows "integrable lborel
    (\<lambda>x. exp (\<i> * of_real (- xi * x)) *
      slp_scaled_gaussian a x)"
proof (rule Bochner_Integration.integrable_bound[
    OF slp_scaled_gaussian_integrable[OF a]])
  show "(\<lambda>x. exp (\<i> * of_real (- xi * x)) *
      slp_scaled_gaussian a x) \<in> borel_measurable lborel"
    by measurable
  show "AE x in lborel.
      norm_class.norm
          (exp (\<i> * of_real (- xi * x)) *
            slp_scaled_gaussian a x)
        \<le> norm_class.norm (slp_scaled_gaussian a x)"
    by (rule AE_I2)
      (simp only: norm_mult norm_exp_i_times mult.left_neutral order_refl)
qed

lemma slp_scaled_gaussian_fourier_integral:
  assumes a: "0 < a"
  shows "integral\<^sup>L lborel
      (\<lambda>x. exp (\<i> * of_real (- xi * x)) *
        slp_scaled_gaussian a x) =
    of_real
      (sqrt (2 * pi) *
        exp (- ((xi / sqrt a) ^ 2) / 2)) /\<^sub>R sqrt a"
proof -
  let ?r = "sqrt a"
  let ?eta = "xi / ?r"
  let ?base =
    "\<lambda>y. exp (\<i> * of_real (- ?eta * y)) *
      slp_standard_gaussian y"
  let ?target =
    "\<lambda>x. exp (\<i> * of_real (- xi * x)) *
      slp_scaled_gaussian a x"
  have r_positive: "0 < ?r"
    using a by simp
  have r_nonzero: "?r \<noteq> 0"
    using r_positive by simp
  have base_value:
      "integral\<^sup>L lborel ?base =
        of_real
          (sqrt (2 * pi) * exp (- (?eta ^ 2) / 2))"
    by (rule slp_standard_gaussian_fourier_integral)
  have pullback_identity:
      "(\<lambda>x. ?base (0 + ?r * x)) = ?target"
  proof (rule ext)
    fix x
    have phase: "- ?eta * (?r * x) = - xi * x"
      using r_nonzero by simp
    show "?base (0 + ?r * x) = ?target x"
      using phase slp_scaled_gaussian_pullback[OF a, of x]
      by simp
  qed
  have affine:
      "integral\<^sup>L lborel ?base =
        \<bar>?r\<bar> *\<^sub>R
          integral\<^sup>L lborel (\<lambda>x. ?base (0 + ?r * x))"
    by (rule lborel_integral_real_affine[OF r_nonzero])
  have scaled:
      "?r *\<^sub>R integral\<^sup>L lborel ?target =
        of_real
          (sqrt (2 * pi) * exp (- (?eta ^ 2) / 2))"
    using affine base_value pullback_identity r_positive
    by simp
  show ?thesis
    using scaled r_nonzero
    by (simp add: divideR_right)
qed

lemma slp_scaled_gaussian_integral:
  assumes a: "0 < a"
  shows "integral\<^sup>L lborel (slp_scaled_gaussian a) =
    of_real (sqrt (2 * pi)) /\<^sub>R sqrt a"
  using slp_scaled_gaussian_fourier_integral[OF a, of 0]
  by simp

end
