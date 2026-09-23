theory Inverse_Schrodinger_Lp_Damped_Center_Fourier_Closed
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Hyperbolic_Decay_Normalization"
begin

section \<open>The closed damped center-kernel Fourier transform\<close>

lemma slp_hyperbolic_gaussian_coefficient:
  assumes eps: "0 < eps"
  shows "(1 / 2) *
      (sqrt (2 * pi) *
        exp (- (((slp_hyperbolic_freq_plus xi) ^ 2 * eps) /
          (2 * (eps ^ 2 + tau ^ 2)))) / sqrt eps) *
      (sqrt (2 * pi) *
        exp (- ((slp_hyperbolic_freq_minus xi /
          sqrt (slp_hyperbolic_second_scale eps tau)) ^ 2) / 2) /
        sqrt (slp_hyperbolic_second_scale eps tau)) =
    pi * exp (- eps *
      ((xi $ (0 :: 2)) ^ 2 + (xi $ (1 :: 2)) ^ 2) /
      (4 * (eps ^ 2 + tau ^ 2))) /
      sqrt (eps ^ 2 + tau ^ 2)"
proof -
  let ?D = "eps ^ 2 + tau ^ 2"
  let ?S = "slp_hyperbolic_second_scale eps tau"
  let ?E1 = "- (((slp_hyperbolic_freq_plus xi) ^ 2 * eps) /
    (2 * ?D))"
  let ?E2 = "- ((slp_hyperbolic_freq_minus xi / sqrt ?S) ^ 2) / 2"
  let ?E = "- eps *
    ((xi $ (0 :: 2)) ^ 2 + (xi $ (1 :: 2)) ^ 2) / (4 * ?D)"
  have root_mass: "sqrt (2 * pi) * sqrt (2 * pi) = 2 * pi"
    by simp
  have decay_sum: "?E1 + ?E2 = ?E"
    using slp_hyperbolic_decay_exponent[OF eps, of xi tau]
    by (simp only: diff_conv_add_uminus)
  have exponential: "exp ?E1 * exp ?E2 = exp ?E"
    by (simp only: exp_add[symmetric] decay_sum)
  have numerator:
      "(1 / 2) * (sqrt (2 * pi) * exp ?E1) *
          (sqrt (2 * pi) * exp ?E2) =
        pi * exp ?E"
  proof -
    have "(1 / 2) * (sqrt (2 * pi) * exp ?E1) *
          (sqrt (2 * pi) * exp ?E2) =
        (1 / 2) * (sqrt (2 * pi) * sqrt (2 * pi)) *
          (exp ?E1 * exp ?E2)"
      by (simp only: mult_ac)
    also have "... = (1 / 2) * (2 * pi) * exp ?E"
      by (simp only: root_mass exponential)
    also have "... = pi * exp ?E"
      by simp
    finally show ?thesis .
  qed
  have quotient_regroup:
      "(1 / 2) * (a / r) * (b / s) =
        ((1 / 2) * a * b) / (r * s)"
      for a b r s :: real
  proof -
    have "(1 / 2) * (a / r) * (b / s) =
        (((1 / 2) * a) / r) * (b / s)"
      by (simp only: times_divide_eq_right)
    also have "... = ((((1 / 2) * a) / r) * b) / s"
      by (simp only: times_divide_eq_right)
    also have "... = ((((1 / 2) * a) * b) / r) / s"
      by (simp only: times_divide_eq_left)
    also have "... = ((1 / 2) * a * b) / (r * s)"
      by (simp only: divide_divide_eq_left)
    finally show ?thesis .
  qed
  have root_product:
      "sqrt eps * sqrt ?S = sqrt ?D"
    by (rule slp_hyperbolic_sqrt_scale_product[OF eps])
  have "(1 / 2) *
        ((sqrt (2 * pi) * exp ?E1) / sqrt eps) *
        ((sqrt (2 * pi) * exp ?E2) / sqrt ?S) =
      ((1 / 2) * (sqrt (2 * pi) * exp ?E1) *
        (sqrt (2 * pi) * exp ?E2)) /
        (sqrt eps * sqrt ?S)"
    by (rule quotient_regroup)
  also have "... = (pi * exp ?E) / (sqrt eps * sqrt ?S)"
    by (simp only: numerator)
  also have "... = (pi * exp ?E) / sqrt ?D"
    by (simp only: root_product)
  finally show ?thesis .
qed

lemma slp_damped_center_fourier_transform_closed:
  assumes eps: "0 < eps"
  shows "slp_fourier_transform
      (slp_damped_center_kernel eps tau) xi =
    of_real
      (pi * exp (- eps *
        ((xi $ (0 :: 2)) ^ 2 + (xi $ (1 :: 2)) ^ 2) /
        (4 * (eps ^ 2 + tau ^ 2))) /
        sqrt (eps ^ 2 + tau ^ 2)) *
      exp (\<i> * of_real
        (- (tau * slp_center_phase 0 xi /
          (4 * (eps ^ 2 + tau ^ 2)))))"
proof -
  let ?D = "eps ^ 2 + tau ^ 2"
  let ?S = "slp_hyperbolic_second_scale eps tau"
  let ?C1 = "sqrt (2 * pi) *
    exp (- (((slp_hyperbolic_freq_plus xi) ^ 2 * eps) / (2 * ?D)))"
  let ?C2 = "sqrt (2 * pi) *
    exp (- ((slp_hyperbolic_freq_minus xi / sqrt ?S) ^ 2) / 2)"
  let ?R = "pi * exp (- eps *
    ((xi $ (0 :: 2)) ^ 2 + (xi $ (1 :: 2)) ^ 2) / (4 * ?D)) /
    sqrt ?D"
  let ?P = "exp (\<i> * of_real
    (- slp_hyperbolic_freq_minus xi *
      slp_hyperbolic_second_center eps tau xi))"
  let ?Q = "exp (\<i> * of_real
    (- (tau * slp_center_phase 0 xi / (4 * ?D))))"
  have coefficient:
      "(1 / 2) * (?C1 / sqrt eps) * (?C2 / sqrt ?S) = ?R"
    by (rule slp_hyperbolic_gaussian_coefficient[OF eps])
  have phase_argument:
      "- slp_hyperbolic_freq_minus xi *
          slp_hyperbolic_second_center eps tau xi =
        - (tau * slp_center_phase 0 xi / (4 * ?D))"
    by (rule slp_hyperbolic_translation_phase[OF eps])
  have phase: "?P = ?Q"
    by (simp only: phase_argument)
  have complex_regroup:
      "(1 / 2) *\<^sub>R
          ((of_real a /\<^sub>R r) *
            (z * (of_real b /\<^sub>R s))) =
        of_real ((1 / 2) * (a / r) * (b / s)) * z"
      for a b r s :: real and z :: complex
  proof -
    have divide_lift:
        "(of_real c :: complex) /\<^sub>R t = of_real (c / t)"
        for c t :: real
    proof -
      have "of_real c /\<^sub>R t = inverse t *\<^sub>R of_real c"
        by (simp only: divideR_right)
      also have "... = of_real (inverse t) * of_real c"
        by (simp only: scaleR_conv_of_real)
      also have "... = of_real (inverse t * c)"
        by (simp only: of_real_mult)
      also have "... = of_real (c / t)"
        by (simp only: divide_inverse mult.commute)
      finally show ?thesis .
    qed
    have commute_b:
        "z * of_real (b / s) = of_real (b / s) * z"
      by (rule mult.commute)
    have divide_a:
        "(of_real a :: complex) /\<^sub>R r = of_real (a / r)"
      by (rule divide_lift)
    have divide_b:
        "(of_real b :: complex) /\<^sub>R s = of_real (b / s)"
      by (rule divide_lift)
    have "(1 / 2) *\<^sub>R
          ((of_real a /\<^sub>R r) *
            (z * (of_real b /\<^sub>R s))) =
        (1 / 2) *\<^sub>R
          (of_real (a / r) * (z * of_real (b / s)))"
      by (subst divide_a, subst divide_b, rule refl)
    also have "... = of_real (1 / 2) *
        (of_real (a / r) * (z * of_real (b / s)))"
      by (simp only: scaleR_conv_of_real)
    also have "... = of_real (1 / 2) *
        (of_real (a / r) * (of_real (b / s) * z))"
      by (simp only: commute_b)
    also have "... =
        of_real ((1 / 2) * (a / r) * (b / s)) * z"
      by (simp only: of_real_mult mult.assoc)
    finally show ?thesis .
  qed
  have "slp_fourier_transform
      (slp_damped_center_kernel eps tau) xi =
    (1 / 2) *\<^sub>R
      ((of_real ?C1 /\<^sub>R sqrt eps) *
        (?P * (of_real ?C2 /\<^sub>R sqrt ?S)))"
    by (rule slp_damped_center_fourier_transform_hyperbolic_raw[OF eps])
  also have "... =
      of_real ((1 / 2) * (?C1 / sqrt eps) * (?C2 / sqrt ?S)) * ?P"
    by (rule complex_regroup)
  also have "... = of_real ?R * ?P"
    by (simp only: coefficient)
  also have "... = of_real ?R * ?Q"
    by (simp only: phase)
  finally show ?thesis .
qed

end
