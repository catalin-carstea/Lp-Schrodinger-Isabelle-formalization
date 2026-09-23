theory Inverse_Schrodinger_Lp_Fourier_Hyperbolic_Second_Fiber
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Fourier_Hyperbolic_First_Fiber"
begin

section \<open>The shifted second real-Gaussian fiber\<close>

definition slp_hyperbolic_second_scale :: "real \<Rightarrow> real \<Rightarrow> real"
where
  "slp_hyperbolic_second_scale eps tau =
    (eps ^ 2 + tau ^ 2) / eps"

definition slp_hyperbolic_second_center ::
  "real \<Rightarrow> real \<Rightarrow> slp_point \<Rightarrow> real"
where
  "slp_hyperbolic_second_center eps tau xi =
    slp_hyperbolic_freq_plus xi * tau / (eps ^ 2 + tau ^ 2)"

definition slp_hyperbolic_second_fiber ::
  "real \<Rightarrow> real \<Rightarrow> slp_point \<Rightarrow> real \<Rightarrow> complex"
where
  "slp_hyperbolic_second_fiber eps tau xi v =
    exp (\<i> * of_real (- slp_hyperbolic_freq_minus xi * v)) *
      slp_scaled_gaussian (slp_hyperbolic_second_scale eps tau)
        (v - slp_hyperbolic_second_center eps tau xi)"

definition slp_hyperbolic_post_first ::
  "real \<Rightarrow> real \<Rightarrow> slp_point \<Rightarrow> real \<Rightarrow> complex"
where
  "slp_hyperbolic_post_first eps tau xi v =
    slp_hyperbolic_outer_factor eps xi v *
      integral\<^sup>L lborel
        (slp_hyperbolic_first_fiber eps tau xi v)"

lemma slp_hyperbolic_second_scale_positive:
  assumes eps: "0 < eps"
  shows "0 < slp_hyperbolic_second_scale eps tau"
proof -
  have numerator: "0 < eps ^ 2 + tau ^ 2"
    using eps by (intro add_pos_nonneg) simp_all
  show ?thesis
    unfolding slp_hyperbolic_second_scale_def
    by (rule divide_pos_pos[OF numerator eps])
qed

lemma slp_hyperbolic_complete_second_square:
  assumes eps: "0 < eps"
  shows "- eps * v ^ 2 / 2 -
      (((slp_hyperbolic_freq_plus xi - tau * v) / sqrt eps) ^ 2) / 2 =
    - slp_hyperbolic_second_scale eps tau *
        (v - slp_hyperbolic_second_center eps tau xi) ^ 2 / 2 -
      (slp_hyperbolic_freq_plus xi) ^ 2 * eps /
        (2 * (eps ^ 2 + tau ^ 2))"
proof -
  have eps_nonzero: "eps \<noteq> 0"
    using eps by simp
  have denominator_positive: "0 < eps ^ 2 + tau ^ 2"
    using eps by (intro add_pos_nonneg) simp_all
  have denominator_nonzero: "eps ^ 2 + tau ^ 2 \<noteq> 0"
    by (rule not_sym, rule less_imp_neq[OF denominator_positive])
  have sqrt_square: "sqrt eps ^ 2 = eps"
    using eps by simp
  have quotient_square:
      "(((slp_hyperbolic_freq_plus xi - tau * v) / sqrt eps) ^ 2) / 2 =
        (((slp_hyperbolic_freq_plus xi - tau * v) ^ 2) / eps) / 2"
    by (simp only: power_divide sqrt_square)
  have rational_completion:
      "- eps * v ^ 2 / 2 -
          (((slp_hyperbolic_freq_plus xi - tau * v) ^ 2) / eps) / 2 =
        - ((eps ^ 2 + tau ^ 2) / eps) *
            (v - slp_hyperbolic_freq_plus xi * tau /
              (eps ^ 2 + tau ^ 2)) ^ 2 / 2 -
          (slp_hyperbolic_freq_plus xi) ^ 2 * eps /
            (2 * (eps ^ 2 + tau ^ 2))"
  proof -
    let ?A = "slp_hyperbolic_freq_plus xi"
    let ?D = "eps ^ 2 + tau ^ 2"
    let ?K = "2 * eps * ?D"
    have K_nonzero: "?K \<noteq> 0"
      by (simp add: eps_nonzero denominator_nonzero)
    have quotient_cancel:
        "(?A * tau / ?D) * ?D = ?A * tau"
      by (rule iffD1[OF nonzero_eq_divide_eq[OF denominator_nonzero]],
          rule refl)
    have eps_quotient_cancel: "(x / eps) * eps = x" for x :: real
      by (rule iffD1[OF nonzero_eq_divide_eq[OF eps_nonzero]], rule refl)
    have denominator_quotient_cancel: "(x / ?D) * ?D = x" for x :: real
      by (rule iffD1[OF nonzero_eq_divide_eq[OF denominator_nonzero]],
          rule refl)
    have eps_scaled_quotient_cancel:
        "(- (x / eps) * y) * eps = - x * y" for x y :: real
    proof -
      have "(- (x / eps) * y) * eps =
          - (((x / eps) * y) * eps)"
        by (simp only: mult_minus_left)
      also have "... = - (((x / eps) * eps) * y)"
        by (simp only: mult_ac)
      also have "... = - (x * y)"
        by (simp only: eps_quotient_cancel)
      also have "... = - x * y"
        by (simp only: mult_minus_left)
      finally show ?thesis .
    qed
    have shifted_scaled:
        "(v - ?A * tau / ?D) * ?D = v * ?D - ?A * tau"
      unfolding left_diff_distrib
      by (simp only: quotient_cancel)
    have second_division:
        "?A ^ 2 * eps / (2 * ?D) = (?A ^ 2 * eps / ?D) / 2"
      by (simp only: divide_divide_eq_left mult.commute)
    have half_regroup:
        "(x / 2 - y / 2) * (2 * e * d) = (x * e - y * e) * d"
      for x y e d :: real
      by (simp add: divide_simps algebra_simps)
    have half_regroup_cross:
        "(x / 2 - y / 2) * (2 * e * d) =
          (x * e) * d - (y * d) * e"
      for x y e d :: real
      by (simp add: divide_simps algebra_simps)
    have square_regroup:
        "((- d * (s ^ 2)) * d) - ((a * e) * e) =
          - ((s * d) ^ 2) - (a * (e ^ 2))"
      for d s a e :: real
      by (simp only: power2_eq_square mult_minus_left mult_minus_right mult_ac)
    have left_scaled:
        "(- eps * v ^ 2 / 2 - ((?A - tau * v) ^ 2 / eps) / 2) * ?K =
          - ?D * (eps ^ 2 * v ^ 2 + (?A - tau * v) ^ 2)"
    proof -
      have rearranged:
          "(- eps * v ^ 2 / 2 - ((?A - tau * v) ^ 2 / eps) / 2) * ?K =
            ((- eps * v ^ 2) * eps -
              (((?A - tau * v) ^ 2 / eps) * eps)) * ?D"
        by (rule half_regroup)
      from rearranged have
        "(- eps * v ^ 2 / 2 - ((?A - tau * v) ^ 2 / eps) / 2) * ?K =
          ((- eps * v ^ 2) * eps -
            (((?A - tau * v) ^ 2 / eps) * eps)) * ?D" .
      also have "... =
          ((- eps * v ^ 2) * eps - (?A - tau * v) ^ 2) * ?D"
        by (simp only: eps_quotient_cancel)
      also have "... =
          - ?D * (eps ^ 2 * v ^ 2 + (?A - tau * v) ^ 2)"
        by (simp only: power2_eq_square algebra_simps mult_minus_left
            mult_minus_right mult_ac)
      finally show ?thesis .
    qed
    have right_scaled:
        "(- (?D / eps) * (v - ?A * tau / ?D) ^ 2 / 2 -
            ?A ^ 2 * eps / (2 * ?D)) * ?K =
          (- (((v - ?A * tau / ?D) * ?D) ^ 2)) -
            ((?A ^ 2) * (eps ^ 2))"
    proof -
      have rearranged:
          "(- (?D / eps) * (v - ?A * tau / ?D) ^ 2 / 2 -
              (?A ^ 2 * eps / ?D) / 2) * ?K =
            ((- (?D / eps) * (v - ?A * tau / ?D) ^ 2) * eps) * ?D -
              ((?A ^ 2 * eps / ?D) * ?D) * eps"
        by (rule half_regroup_cross)
      have "(- (?D / eps) * (v - ?A * tau / ?D) ^ 2 / 2 -
            ?A ^ 2 * eps / (2 * ?D)) * ?K =
          (- (?D / eps) * (v - ?A * tau / ?D) ^ 2 / 2 -
            (?A ^ 2 * eps / ?D) / 2) * ?K"
        by (simp only: second_division)
      also have "... =
          ((- (?D / eps) * (v - ?A * tau / ?D) ^ 2) * eps) * ?D -
            ((?A ^ 2 * eps / ?D) * ?D) * eps"
        by (rule rearranged)
      also have "... =
          ((- ?D * (v - ?A * tau / ?D) ^ 2) * ?D) -
            (?A ^ 2 * eps) * eps"
        by (simp only: eps_scaled_quotient_cancel
            denominator_quotient_cancel)
      also have "... =
          (- (((v - ?A * tau / ?D) * ?D) ^ 2)) -
            ((?A ^ 2) * (eps ^ 2))"
        by (rule square_regroup)
      finally show ?thesis .
    qed
    have numerator_identity:
        "- ?D * (eps ^ 2 * v ^ 2 + (?A - tau * v) ^ 2) =
          (- ((v * ?D - ?A * tau) ^ 2)) -
            ((?A ^ 2) * (eps ^ 2))"
      by (simp only: power2_eq_square algebra_simps mult_minus_left
          mult_minus_right mult_ac)
    have scaled_equality:
        "(- eps * v ^ 2 / 2 - ((?A - tau * v) ^ 2 / eps) / 2) * ?K =
          (- (?D / eps) * (v - ?A * tau / ?D) ^ 2 / 2 -
            ?A ^ 2 * eps / (2 * ?D)) * ?K"
      using left_scaled right_scaled shifted_scaled numerator_identity
      by simp
    have cancel_iff:
        "((- eps * v ^ 2 / 2 - ((?A - tau * v) ^ 2 / eps) / 2) * ?K =
            (- (?D / eps) * (v - ?A * tau / ?D) ^ 2 / 2 -
              ?A ^ 2 * eps / (2 * ?D)) * ?K) \<longleftrightarrow>
          (- eps * v ^ 2 / 2 - ((?A - tau * v) ^ 2 / eps) / 2 =
            - (?D / eps) * (v - ?A * tau / ?D) ^ 2 / 2 -
              ?A ^ 2 * eps / (2 * ?D))"
      by (rule mult_right_cancel[OF K_nonzero])
    show ?thesis
      using scaled_equality cancel_iff by blast
  qed
  show ?thesis
    unfolding slp_hyperbolic_second_scale_def
      slp_hyperbolic_second_center_def
    using quotient_square rational_completion
    by simp
qed

lemma slp_hyperbolic_post_first_factor:
  assumes eps: "0 < eps"
  shows "slp_hyperbolic_post_first eps tau xi v =
    (of_real
      (sqrt (2 * pi) *
        exp (- (((slp_hyperbolic_freq_plus xi) ^ 2 * eps) /
          (2 * (eps ^ 2 + tau ^ 2))))) /\<^sub>R sqrt eps) *
      slp_hyperbolic_second_fiber eps tau xi v"
proof -
  have completed:
      "- eps * v ^ 2 / 2 -
          (((slp_hyperbolic_freq_plus xi - tau * v) /
            sqrt eps) ^ 2) / 2 =
        - slp_hyperbolic_second_scale eps tau *
            (v - slp_hyperbolic_second_center eps tau xi) ^ 2 / 2 -
          (slp_hyperbolic_freq_plus xi) ^ 2 * eps /
            (2 * (eps ^ 2 + tau ^ 2))"
    by (rule slp_hyperbolic_complete_second_square[OF eps])
  have exponent_sum:
      "- eps * v ^ 2 / 2 +
          - (((slp_hyperbolic_freq_plus xi - tau * v) /
            sqrt eps) ^ 2) / 2 =
        - slp_hyperbolic_second_scale eps tau *
            (v - slp_hyperbolic_second_center eps tau xi) ^ 2 / 2 +
          - (((slp_hyperbolic_freq_plus xi) ^ 2 * eps) /
            (2 * (eps ^ 2 + tau ^ 2)))"
    using completed
    by (simp only: diff_conv_add_uminus)
  have exponential_product:
      "exp (- eps * v ^ 2 / 2) *
          exp (- (((slp_hyperbolic_freq_plus xi - tau * v) /
            sqrt eps) ^ 2) / 2) =
        exp (- slp_hyperbolic_second_scale eps tau *
          (v - slp_hyperbolic_second_center eps tau xi) ^ 2 / 2) *
        exp (- (((slp_hyperbolic_freq_plus xi) ^ 2 * eps) /
          (2 * (eps ^ 2 + tau ^ 2))))"
    by (simp only: exp_add[symmetric] exponent_sum)
  have complex_exponential_product:
      "of_real (exp (- eps * v ^ 2 / 2)) *
          of_real (exp (- (((slp_hyperbolic_freq_plus xi - tau * v) /
            sqrt eps) ^ 2) / 2)) =
        of_real (exp (- slp_hyperbolic_second_scale eps tau *
          (v - slp_hyperbolic_second_center eps tau xi) ^ 2 / 2)) *
        of_real (exp (- (((slp_hyperbolic_freq_plus xi) ^ 2 * eps) /
          (2 * (eps ^ 2 + tau ^ 2)))))"
    using exponential_product
    by (simp only: of_real_mult[symmetric])
  have real_product:
      "exp (- eps * v ^ 2 / 2) *
          (sqrt (2 * pi) *
            exp (- (((slp_hyperbolic_freq_plus xi - tau * v) /
              sqrt eps) ^ 2) / 2)) =
        (sqrt (2 * pi) *
          exp (- (((slp_hyperbolic_freq_plus xi) ^ 2 * eps) /
            (2 * (eps ^ 2 + tau ^ 2))))) *
          exp (- slp_hyperbolic_second_scale eps tau *
            (v - slp_hyperbolic_second_center eps tau xi) ^ 2 / 2)"
    by (simp only: mult_ac exponential_product)
  show ?thesis
    unfolding slp_hyperbolic_post_first_def
      slp_hyperbolic_outer_factor_def
      slp_hyperbolic_second_fiber_def
      slp_scaled_gaussian_def
      slp_hyperbolic_first_fiber_integral[OF eps]
    by (simp only: divideR_right scaleR_conv_of_real of_real_mult
        complex_exponential_product mult_ac)
qed

lemma slp_hyperbolic_second_fiber_integrable:
  assumes eps: "0 < eps"
  shows "integrable lborel
    (slp_hyperbolic_second_fiber eps tau xi)"
proof -
  let ?a = "slp_hyperbolic_second_scale eps tau"
  let ?b = "slp_hyperbolic_freq_minus xi"
  let ?c = "slp_hyperbolic_second_center eps tau xi"
  let ?base =
    "\<lambda>w. exp (\<i> * of_real (- ?b * w)) *
      slp_scaled_gaussian ?a w"
  have a_positive: "0 < ?a"
    by (rule slp_hyperbolic_second_scale_positive[OF eps])
  have base_integrable: "integrable lborel ?base"
    by (rule slp_scaled_gaussian_fourier_integrable[OF a_positive])
  have translated_integrable:
      "integrable lborel (\<lambda>v. ?base (- ?c + 1 * v))"
    by (rule lborel_integrable_real_affine[OF base_integrable]) simp
  have phase_identity:
      "\<i> * of_real (- ?b * v) =
        \<i> * of_real (- ?b * ?c) +
          \<i> * of_real (- ?b * (- ?c + v))" for v
    by (simp add: algebra_simps)
  have phase_product:
      "exp (\<i> * of_real (- ?b * v)) =
        exp (\<i> * of_real (- ?b * ?c)) *
          exp (\<i> * of_real (- ?b * (- ?c + v)))" for v
    using phase_identity[of v]
    by (simp only: exp_add)
  have shifted_phase:
      "exp (\<i> * of_real (- ?b * (- ?c + v))) =
        exp (\<i> * of_real (- ?b * (v - ?c)))" for v
    by simp
  have function_identity:
      "slp_hyperbolic_second_fiber eps tau xi =
        (\<lambda>v. exp (\<i> * of_real (- ?b * ?c)) *
          ?base (- ?c + 1 * v))"
  proof (rule ext)
    fix v
    have shift: "- ?c + 1 * v = v - ?c"
      by simp
    show "slp_hyperbolic_second_fiber eps tau xi v =
        exp (\<i> * of_real (- ?b * ?c)) *
          ?base (- ?c + 1 * v)"
      unfolding slp_hyperbolic_second_fiber_def shift
      apply (subst phase_product)
      apply (subst shifted_phase)
      by (rule mult.assoc)
  qed
  have product_integrable:
      "integrable lborel
        (\<lambda>v. exp (\<i> * of_real (- ?b * ?c)) *
          ?base (- ?c + 1 * v))"
    by (rule Bochner_Integration.integrable_mult_right)
      (simp only: translated_integrable)
  show ?thesis
    using product_integrable by (simp only: function_identity)
qed

lemma slp_hyperbolic_second_fiber_integral:
  assumes eps: "0 < eps"
  shows "integral\<^sup>L lborel
      (slp_hyperbolic_second_fiber eps tau xi) =
    exp (\<i> * of_real
      (- slp_hyperbolic_freq_minus xi *
        slp_hyperbolic_second_center eps tau xi)) *
    (of_real
      (sqrt (2 * pi) *
        exp (- ((slp_hyperbolic_freq_minus xi /
          sqrt (slp_hyperbolic_second_scale eps tau)) ^ 2) / 2)) /\<^sub>R
      sqrt (slp_hyperbolic_second_scale eps tau))"
proof -
  let ?a = "slp_hyperbolic_second_scale eps tau"
  let ?b = "slp_hyperbolic_freq_minus xi"
  let ?c = "slp_hyperbolic_second_center eps tau xi"
  let ?base =
    "\<lambda>w. exp (\<i> * of_real (- ?b * w)) *
      slp_scaled_gaussian ?a w"
  have a_positive: "0 < ?a"
    by (rule slp_hyperbolic_second_scale_positive[OF eps])
  have base_integrable: "integrable lborel ?base"
    by (rule slp_scaled_gaussian_fourier_integrable[OF a_positive])
  have translated_integrable:
      "integrable lborel (\<lambda>v. ?base (- ?c + 1 * v))"
    by (rule lborel_integrable_real_affine[OF base_integrable]) simp
  have base_value:
      "integral\<^sup>L lborel ?base =
        of_real
          (sqrt (2 * pi) *
            exp (- ((?b / sqrt ?a) ^ 2) / 2)) /\<^sub>R sqrt ?a"
    by (rule slp_scaled_gaussian_fourier_integral[OF a_positive])
  have affine:
      "integral\<^sup>L lborel ?base =
        integral\<^sup>L lborel (\<lambda>v. ?base (- ?c + 1 * v))"
    using lborel_integral_real_affine[of 1 ?base "- ?c"]
    by simp
  have translated_value:
      "integral\<^sup>L lborel (\<lambda>v. ?base (- ?c + 1 * v)) =
        of_real
          (sqrt (2 * pi) *
            exp (- ((?b / sqrt ?a) ^ 2) / 2)) /\<^sub>R sqrt ?a"
    by (rule trans[OF affine[symmetric] base_value])
  have phase_identity:
      "\<i> * of_real (- ?b * v) =
        \<i> * of_real (- ?b * ?c) +
          \<i> * of_real (- ?b * (- ?c + v))" for v
    by (simp add: algebra_simps)
  have phase_product:
      "exp (\<i> * of_real (- ?b * v)) =
        exp (\<i> * of_real (- ?b * ?c)) *
          exp (\<i> * of_real (- ?b * (- ?c + v)))" for v
    using phase_identity[of v]
    by (simp only: exp_add)
  have shifted_phase:
      "exp (\<i> * of_real (- ?b * (- ?c + v))) =
        exp (\<i> * of_real (- ?b * (v - ?c)))" for v
    by simp
  have function_identity:
      "slp_hyperbolic_second_fiber eps tau xi =
        (\<lambda>v. exp (\<i> * of_real (- ?b * ?c)) *
          ?base (- ?c + 1 * v))"
  proof (rule ext)
    fix v
    have shift: "- ?c + 1 * v = v - ?c"
      by simp
    show "slp_hyperbolic_second_fiber eps tau xi v =
        exp (\<i> * of_real (- ?b * ?c)) *
          ?base (- ?c + 1 * v)"
      unfolding slp_hyperbolic_second_fiber_def shift
      apply (subst phase_product)
      apply (subst shifted_phase)
      by (rule mult.assoc)
  qed
  show ?thesis
    unfolding function_identity
    using translated_integrable translated_value
    by simp
qed

end
