theory Inverse_Schrodinger_Lp_Fourier_Radial_Gaussian
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Fourier_Planar_Gaussian"
begin

section \<open>Radial normalization of the planar Gaussian\<close>

definition slp_planar_radial_gaussian ::
  "real \<Rightarrow> slp_point \<Rightarrow> complex"
where
  "slp_planar_radial_gaussian a x =
    of_real (exp (- a * (Real_Vector_Spaces.norm x) ^ 2 / 2))"

lemma slp_planar_norm_square:
  fixes x :: slp_point
  shows "(Real_Vector_Spaces.norm x) ^ 2 =
    (x $ 0) ^ 2 + (x $ 1) ^ 2"
proof -
  have universe_two: "(UNIV :: 2 set) = {0, 1}"
    using UNIV_2 by auto
  have sum_nonnegative:
      "0 \<le> (\<Sum>i\<in>(UNIV::2 set). (x $ i) ^ 2)"
    by (rule sum_nonneg) simp
  have sum_two:
      "(\<Sum>i\<in>(UNIV::2 set).
          (norm_class.norm (x $ i)) ^ 2) =
        (x $ 0) ^ 2 + (x $ 1) ^ 2"
    unfolding universe_two by simp
  show ?thesis
    by (simp add: norm_vec_def L2_set_def universe_two
        real_sqrt_pow2[OF sum_nonnegative])
qed

lemma slp_planar_radial_gaussian_product:
  "slp_planar_radial_gaussian a x =
    slp_planar_scaled_gaussian a x"
proof -
  have universe_two: "(UNIV :: 2 set) = {0, 1}"
    using UNIV_2 by auto
  have exponent:
      "- a * (Real_Vector_Spaces.norm x) ^ 2 / 2 =
        (- a * (x $ 0) ^ 2 / 2) +
        (- a * (x $ 1) ^ 2 / 2)"
  proof -
    have norm_square:
        "(Real_Vector_Spaces.norm x) ^ 2 =
          (x $ 0) ^ 2 + (x $ 1) ^ 2"
      by (rule slp_planar_norm_square)
    show ?thesis
      unfolding norm_square
      by (simp only: ring_distribs add_divide_distrib minus_add_distrib)
  qed
  have product_two:
      "(\<Prod>i\<in>(UNIV::2 set).
          slp_scaled_gaussian a (x $ i)) =
        slp_scaled_gaussian a (x $ 0) *
          slp_scaled_gaussian a (x $ 1)"
    unfolding universe_two by simp
  have exponential:
      "of_real
          (exp ((- a * (x $ 0) ^ 2 / 2) +
            (- a * (x $ 1) ^ 2 / 2))) =
        of_real (exp (- a * (x $ 0) ^ 2 / 2)) *
          of_real (exp (- a * (x $ 1) ^ 2 / 2))"
  proof -
    have real_exp:
        "exp ((- a * (x $ 0) ^ 2 / 2) +
            (- a * (x $ 1) ^ 2 / 2)) =
          exp (- a * (x $ 0) ^ 2 / 2) *
            exp (- a * (x $ 1) ^ 2 / 2)"
      by (rule exp_add)
    show ?thesis
      by (simp only: real_exp of_real_mult)
  qed
  show ?thesis
    unfolding slp_planar_radial_gaussian_def
      slp_planar_scaled_gaussian_def
    apply (subst product_two)
    unfolding slp_scaled_gaussian_def
    apply (subst exponent)
    by (rule exponential)
qed

lemma slp_planar_radial_gaussian_measurable[measurable]:
  "slp_planar_radial_gaussian a \<in> borel_measurable lborel"
  unfolding slp_planar_radial_gaussian_def by measurable

lemma slp_planar_radial_gaussian_integrable:
  assumes a: "0 < a"
  shows "integrable lborel (slp_planar_radial_gaussian a)"
proof -
  have function_identity:
      "slp_planar_radial_gaussian a =
        slp_planar_scaled_gaussian a"
    by (rule ext)
      (rule slp_planar_radial_gaussian_product)
  show ?thesis
    using slp_planar_scaled_gaussian_integrable[OF a]
    unfolding function_identity .
qed

lemma slp_planar_radial_gaussian_integral:
  assumes a: "0 < a"
  shows "integral\<^sup>L lborel (slp_planar_radial_gaussian a) =
    of_real (2 * pi / a)"
proof -
  have function_identity:
      "slp_planar_radial_gaussian a =
        slp_planar_scaled_gaussian a"
    by (rule ext)
      (rule slp_planar_radial_gaussian_product)
  have product_value:
      "integral\<^sup>L lborel (slp_planar_radial_gaussian a) =
        (\<Prod>i\<in>(UNIV::2 set).
          of_real (sqrt (2 * pi)) /\<^sub>R sqrt a)"
    using slp_planar_scaled_gaussian_integral[OF a]
    unfolding function_identity .
  have universe_two: "(UNIV :: 2 set) = {0, 1}"
    using UNIV_2 by auto
  have sqrt_a_square: "sqrt a ^ 2 = a"
    using a by simp
  have sqrt_two_pi_square: "sqrt (2 * pi) ^ 2 = 2 * pi"
    by simp
  have inverse_sqrt_square:
      "inverse (sqrt a) ^ 2 = inverse a"
    by (simp only: power_inverse sqrt_a_square)
  have scalar_product:
      "(\<Prod>i\<in>(UNIV::2 set).
          of_real (sqrt (2 * pi)) /\<^sub>R sqrt a) =
        (inverse (sqrt a) * inverse (sqrt a)) *\<^sub>R
          (of_real (sqrt (2 * pi)) *
            of_real (sqrt (2 * pi)))"
    by (simp add: universe_two divideR_right)
  have real_mass:
      "(inverse (sqrt a) * inverse (sqrt a)) *
          (sqrt (2 * pi) * sqrt (2 * pi)) =
        2 * pi / a"
    using inverse_sqrt_square sqrt_two_pi_square
    by (simp only: power2_eq_square divide_inverse mult.commute)
  have normalized:
      "(inverse (sqrt a) * inverse (sqrt a)) *\<^sub>R
          (of_real (sqrt (2 * pi)) *
            of_real (sqrt (2 * pi))) =
        of_real (2 * pi / a)"
  proof -
    have "(inverse (sqrt a) * inverse (sqrt a)) *\<^sub>R
          (of_real (sqrt (2 * pi)) *
            of_real (sqrt (2 * pi))) =
        of_real
          ((inverse (sqrt a) * inverse (sqrt a)) *
            (sqrt (2 * pi) * sqrt (2 * pi)))"
      by (simp only: scaleR_conv_of_real of_real_mult)
    also have "... = of_real (2 * pi / a)"
      by (simp only: real_mass)
    finally show ?thesis .
  qed
  have first:
      "integral\<^sup>L lborel (slp_planar_radial_gaussian a) =
        (inverse (sqrt a) * inverse (sqrt a)) *\<^sub>R
          (of_real (sqrt (2 * pi)) *
            of_real (sqrt (2 * pi)))"
    by (rule trans[OF product_value scalar_product])
  show ?thesis
    by (rule trans[OF first normalized])
qed

lemma slp_planar_radial_gaussian_fourier_integral:
  assumes a: "0 < a"
  shows "slp_fourier_transform (slp_planar_radial_gaussian a) xi =
    of_real ((2 * pi / a) *
      exp (- ((Real_Vector_Spaces.norm xi) ^ 2) / (2 * a)))"
proof -
  have function_identity:
      "slp_planar_radial_gaussian a =
        slp_planar_scaled_gaussian a"
    by (rule ext)
      (rule slp_planar_radial_gaussian_product)
  have product_value:
      "slp_fourier_transform (slp_planar_radial_gaussian a) xi =
        (\<Prod>i\<in>(UNIV::2 set).
          of_real
            (sqrt (2 * pi) *
              exp (- (((xi $ i) / sqrt a) ^ 2) / 2)) /\<^sub>R sqrt a)"
    using slp_planar_scaled_gaussian_fourier_product[OF a, of xi]
    unfolding function_identity .
  have universe_two: "(UNIV :: 2 set) = {0, 1}"
    using UNIV_2 by auto
  have sqrt_a_positive: "0 < sqrt a"
    using a by simp
  have sqrt_a_square: "sqrt a ^ 2 = a"
    using a by simp
  have sqrt_two_pi_square: "sqrt (2 * pi) ^ 2 = 2 * pi"
    by simp
  have norm_square:
      "(Real_Vector_Spaces.norm xi) ^ 2 =
        (xi $ 0) ^ 2 + (xi $ 1) ^ 2"
    by (rule slp_planar_norm_square)
  have inverse_sqrt_square:
      "inverse (sqrt a) ^ 2 = inverse a"
    by (simp only: power_inverse sqrt_a_square)
  have coefficient:
      "(sqrt (2 * pi) / sqrt a) *
          (sqrt (2 * pi) / sqrt a) =
        2 * pi / a"
  proof -
    have "(sqrt (2 * pi) / sqrt a) *
          (sqrt (2 * pi) / sqrt a) =
        sqrt (2 * pi) ^ 2 * inverse (sqrt a) ^ 2"
      by (simp only: divide_inverse power2_eq_square mult_ac)
    also have "... = (2 * pi) * inverse a"
      by (simp only: sqrt_two_pi_square inverse_sqrt_square)
    also have "... = 2 * pi / a"
      by (simp only: divide_inverse)
    finally show ?thesis .
  qed
  have coordinate_sum:
      "((xi $ 0) / sqrt a) ^ 2 +
          ((xi $ 1) / sqrt a) ^ 2 =
        (Real_Vector_Spaces.norm xi) ^ 2 / a"
  proof -
    have "((xi $ 0) / sqrt a) ^ 2 +
          ((xi $ 1) / sqrt a) ^ 2 =
        ((xi $ 0) ^ 2 + (xi $ 1) ^ 2) *
          inverse (sqrt a) ^ 2"
      by (simp only: divide_inverse power_mult_distrib ring_distribs)
    also have "... =
        (Real_Vector_Spaces.norm xi) ^ 2 * inverse a"
      by (simp only: norm_square inverse_sqrt_square)
    also have "... = (Real_Vector_Spaces.norm xi) ^ 2 / a"
      by (simp only: divide_inverse)
    finally show ?thesis .
  qed
  have exponent_identity:
      "- (((xi $ 0) / sqrt a) ^ 2) / 2 +
          - (((xi $ 1) / sqrt a) ^ 2) / 2 =
        - ((Real_Vector_Spaces.norm xi) ^ 2) / (2 * a)"
  proof -
    have "- (((xi $ 0) / sqrt a) ^ 2) / 2 +
          - (((xi $ 1) / sqrt a) ^ 2) / 2 =
        - (((xi $ 0) / sqrt a) ^ 2 +
          ((xi $ 1) / sqrt a) ^ 2) / 2"
      by (simp only: minus_add_distrib add_divide_distrib)
    also have "... =
        - ((Real_Vector_Spaces.norm xi) ^ 2 / a) / 2"
      by (simp only: coordinate_sum)
    also have "... =
        - ((Real_Vector_Spaces.norm xi) ^ 2) / (2 * a)"
    proof -
      have inverse_denominator:
          "inverse a * inverse 2 = inverse (2 * a)"
        by (simp only: inverse_mult_distrib mult.commute)
      show ?thesis
        by (simp only: divide_inverse minus_mult_left mult.assoc
            inverse_denominator)
    qed
    finally show ?thesis .
  qed
  have factor:
      "of_real
          (sqrt (2 * pi) *
            exp (- (((xi $ i) / sqrt a) ^ 2) / 2)) /\<^sub>R sqrt a =
        of_real
          ((sqrt (2 * pi) / sqrt a) *
            exp (- (((xi $ i) / sqrt a) ^ 2) / 2))"
    for i
    by (simp only: divideR_right scaleR_conv_of_real
        divide_inverse of_real_mult mult_ac)
  have exponential_product:
      "exp (- (((xi $ 0) / sqrt a) ^ 2) / 2) *
          exp (- (((xi $ 1) / sqrt a) ^ 2) / 2) =
        exp (- ((Real_Vector_Spaces.norm xi) ^ 2) / (2 * a))"
    by (simp only: exp_add[symmetric] exponent_identity)
  have real_product:
      "((sqrt (2 * pi) / sqrt a) *
          exp (- (((xi $ 0) / sqrt a) ^ 2) / 2)) *
        ((sqrt (2 * pi) / sqrt a) *
          exp (- (((xi $ 1) / sqrt a) ^ 2) / 2)) =
        (2 * pi / a) *
          exp (- ((Real_Vector_Spaces.norm xi) ^ 2) / (2 * a))"
  proof -
    have "((sqrt (2 * pi) / sqrt a) *
          exp (- (((xi $ 0) / sqrt a) ^ 2) / 2)) *
        ((sqrt (2 * pi) / sqrt a) *
          exp (- (((xi $ 1) / sqrt a) ^ 2) / 2)) =
        ((sqrt (2 * pi) / sqrt a) *
          (sqrt (2 * pi) / sqrt a)) *
        (exp (- (((xi $ 0) / sqrt a) ^ 2) / 2) *
          exp (- (((xi $ 1) / sqrt a) ^ 2) / 2))"
      by (simp only: mult_ac)
    also have "... = (2 * pi / a) *
        exp (- ((Real_Vector_Spaces.norm xi) ^ 2) / (2 * a))"
      by (simp only: coefficient exponential_product)
    finally show ?thesis .
  qed
  have product_closed:
      "(\<Prod>i\<in>(UNIV::2 set).
          of_real
            (sqrt (2 * pi) *
              exp (- (((xi $ i) / sqrt a) ^ 2) / 2)) /\<^sub>R sqrt a) =
        of_real ((2 * pi / a) *
          exp (- ((Real_Vector_Spaces.norm xi) ^ 2) / (2 * a)))"
  proof -
    have "(\<Prod>i\<in>(UNIV::2 set).
          of_real
            (sqrt (2 * pi) *
              exp (- (((xi $ i) / sqrt a) ^ 2) / 2)) /\<^sub>R sqrt a) =
        (\<Prod>i\<in>(UNIV::2 set).
          of_real
            ((sqrt (2 * pi) / sqrt a) *
              exp (- (((xi $ i) / sqrt a) ^ 2) / 2)))"
      by (simp only: factor)
    also have "... =
        of_real
          ((sqrt (2 * pi) / sqrt a) *
            exp (- (((xi $ 0) / sqrt a) ^ 2) / 2)) *
        of_real
          ((sqrt (2 * pi) / sqrt a) *
            exp (- (((xi $ 1) / sqrt a) ^ 2) / 2))"
      by (simp add: universe_two)
    also have "... = of_real
        (((sqrt (2 * pi) / sqrt a) *
            exp (- (((xi $ 0) / sqrt a) ^ 2) / 2)) *
          ((sqrt (2 * pi) / sqrt a) *
            exp (- (((xi $ 1) / sqrt a) ^ 2) / 2)))"
      by (simp only: of_real_mult)
    also have "... = of_real ((2 * pi / a) *
        exp (- ((Real_Vector_Spaces.norm xi) ^ 2) / (2 * a)))"
      by (simp only: real_product)
    finally show ?thesis .
  qed
  show ?thesis
    by (rule trans[OF product_value product_closed])
qed

end
