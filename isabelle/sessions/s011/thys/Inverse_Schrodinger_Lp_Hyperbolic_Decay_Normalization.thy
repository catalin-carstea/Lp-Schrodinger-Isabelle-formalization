theory Inverse_Schrodinger_Lp_Hyperbolic_Decay_Normalization
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Hyperbolic_Frequency_Normalization"
begin

section \<open>Real damping-scale and decay normalization\<close>

lemma slp_hyperbolic_sqrt_scale_product:
  fixes eps tau :: real
  assumes eps: "0 < eps"
  shows "sqrt eps * sqrt (slp_hyperbolic_second_scale eps tau) =
    sqrt (eps ^ 2 + tau ^ 2)"
proof -
  have sqrt_eps_nonzero: "sqrt eps \<noteq> 0"
    using eps by simp
  show ?thesis
    unfolding slp_hyperbolic_second_scale_def
    using eps
    by (simp add: real_sqrt_divide sqrt_eps_nonzero)
qed

lemma slp_hyperbolic_decay_exponent:
  assumes eps: "0 < eps"
  shows "- (((slp_hyperbolic_freq_plus xi) ^ 2 * eps) /
      (2 * (eps ^ 2 + tau ^ 2))) -
      ((slp_hyperbolic_freq_minus xi /
        sqrt (slp_hyperbolic_second_scale eps tau)) ^ 2) / 2 =
    - eps * ((xi $ (0 :: 2)) ^ 2 + (xi $ (1 :: 2)) ^ 2) /
      (4 * (eps ^ 2 + tau ^ 2))"
proof -
  let ?D = "eps ^ 2 + tau ^ 2"
  let ?A = "slp_hyperbolic_freq_plus xi"
  let ?B = "slp_hyperbolic_freq_minus xi"
  let ?S = "slp_hyperbolic_second_scale eps tau"
  have denominator_positive: "0 < ?D"
    by (rule slp_hyperbolic_denominator_positive[OF eps])
  have denominator_nonzero: "?D \<noteq> 0"
    by (rule not_sym, rule less_imp_neq[OF denominator_positive])
  have scale_positive: "0 < ?S"
    by (rule slp_hyperbolic_second_scale_positive[OF eps])
  have sqrt_scale_square: "sqrt ?S ^ 2 = ?S"
    using scale_positive by simp
  have minus_term:
      "((?B / sqrt ?S) ^ 2) / 2 =
        ?B ^ 2 * eps / (2 * ?D)"
  proof -
    have "((?B / sqrt ?S) ^ 2) / 2 =
        (?B ^ 2 / ?S) / 2"
      by (simp only: power_divide sqrt_scale_square)
    also have "... =
        (?B ^ 2 / (?D / eps)) / 2"
      unfolding slp_hyperbolic_second_scale_def by simp
    also have "... = ?B ^ 2 * eps / (2 * ?D)"
      by (simp only: divide_divide_eq_right divide_divide_eq_left
          mult.commute)
    finally show ?thesis .
  qed
  have collect:
      "- (?A ^ 2 * eps / (2 * ?D)) -
          (?B ^ 2 * eps / (2 * ?D)) =
        - eps * (?A ^ 2 + ?B ^ 2) / (2 * ?D)"
  proof -
    have numerator:
        "- (?A ^ 2 * eps) - (?B ^ 2 * eps) =
          - eps * (?A ^ 2 + ?B ^ 2)"
      by (simp add: algebra_simps)
    have "- (?A ^ 2 * eps / (2 * ?D)) -
          (?B ^ 2 * eps / (2 * ?D)) =
        (- (?A ^ 2 * eps) - (?B ^ 2 * eps)) / (2 * ?D)"
      by (simp only: minus_divide_left diff_divide_distrib)
    also have "... =
        (- eps * (?A ^ 2 + ?B ^ 2)) / (2 * ?D)"
      by (rule arg_cong[OF numerator,
            where f="\<lambda>x::real. x / (2 * ?D)"])
    finally show ?thesis .
  qed
  have squares:
      "?A ^ 2 + ?B ^ 2 =
        ((xi $ (0 :: 2)) ^ 2 + (xi $ (1 :: 2)) ^ 2) / 2"
    by (rule slp_hyperbolic_frequency_square_sum)
  have "- (?A ^ 2 * eps / (2 * ?D)) -
        ((?B / sqrt ?S) ^ 2) / 2 =
      - (?A ^ 2 * eps / (2 * ?D)) -
        (?B ^ 2 * eps / (2 * ?D))"
    by (simp only: minus_term)
  also have "... = - eps * (?A ^ 2 + ?B ^ 2) / (2 * ?D)"
    by (rule collect)
  also have "... =
      - eps * (((xi $ (0 :: 2)) ^ 2 +
        (xi $ (1 :: 2)) ^ 2) / 2) / (2 * ?D)"
    by (simp only: squares)
  also have "... =
      - eps * ((xi $ (0 :: 2)) ^ 2 + (xi $ (1 :: 2)) ^ 2) /
        (4 * ?D)"
  proof -
    have regroup:
        "- e * (x / 2) / (2 * d) = - e * x / (4 * d)"
        for e x d :: real
      by (simp only: times_divide_eq_right divide_divide_eq_left)
    show ?thesis by (rule regroup)
  qed
  finally show ?thesis .
qed

end
