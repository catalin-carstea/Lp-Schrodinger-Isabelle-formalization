theory Inverse_Schrodinger_Lp_Interpolation_Balancing_Threshold
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_015.Inverse_Schrodinger_Lp_Quantitative_Value_Split_Norms"
begin

section \<open>Positive-rate threshold balancing for the coefficient split\<close>

lemma slp_two_power_balancing_threshold:
  fixes alpha beta theta r F :: real
  assumes alpha_negative: "alpha < 0"
    and beta_positive: "0 < beta"
    and beta_below_one: "beta < 1"
    and rate_positive: "0 < r"
    and size_nonnegative: "0 \<le> F"
    and theta_identity: "theta = - alpha / (beta - alpha)"
  shows
    "\<exists>T>0.
      T powr alpha * F powr (1 - alpha) \<le> r powr theta * F
      \<and> r * T powr beta * F powr (1 - beta) \<le> r powr theta * F"
proof -
  have denominator_positive: "0 < beta - alpha"
    using alpha_negative beta_positive by linarith
  have denominator_nonzero: "beta - alpha \<noteq> 0"
    using denominator_positive by simp
  have one_minus_alpha_positive: "0 < 1 - alpha"
    using alpha_negative by linarith
  have one_minus_beta_positive: "0 < 1 - beta"
    using beta_below_one by linarith

  show ?thesis
  proof (cases "F = 0")
    case True
    show ?thesis
      using one_minus_alpha_positive one_minus_beta_positive
      by (intro exI[where x=1]) (simp add: True)
  next
    case False
    have size_positive: "0 < F"
      using size_nonnegative False by linarith
    let ?gamma = "- 1 / (beta - alpha)"
    let ?T = "F * r powr ?gamma"
    have threshold_positive: "0 < ?T"
      using size_positive rate_positive by simp
    have high_rate_exponent: "?gamma * alpha = theta"
      using theta_identity denominator_nonzero
      by (simp add: field_simps)
    have low_rate_exponent: "1 + ?gamma * beta = theta"
      using theta_identity denominator_nonzero
      by (simp add: field_simps)
    have high_source_product:
        "F powr alpha * F powr (1 - alpha) = F"
      using size_positive
      by (subst powr_add[symmetric]) simp
    have low_source_product:
        "F powr beta * F powr (1 - beta) = F"
      using size_positive
      by (subst powr_add[symmetric]) simp
    have high_threshold_power:
        "?T powr alpha = F powr alpha * r powr (?gamma * alpha)"
      by (simp only: powr_mult powr_powr)
    have low_threshold_power:
        "?T powr beta = F powr beta * r powr (?gamma * beta)"
      by (simp only: powr_mult powr_powr)
    have low_rate_product:
        "r * r powr (?gamma * beta) = r powr theta"
    proof -
      have "r * r powr (?gamma * beta) =
          r powr 1 * r powr (?gamma * beta)"
        using rate_positive by simp
      also have "... = r powr (1 + ?gamma * beta)"
        by (rule powr_add[symmetric])
      also have "... = r powr theta"
        using low_rate_exponent by simp
      finally show ?thesis .
    qed
    have high_equality:
        "?T powr alpha * F powr (1 - alpha) = r powr theta * F"
    proof -
      have "?T powr alpha * F powr (1 - alpha) =
          r powr (?gamma * alpha) *
            (F powr alpha * F powr (1 - alpha))"
        by (simp only: high_threshold_power mult.assoc mult.commute
            mult.left_commute)
      also have "... = r powr theta * F"
        using high_rate_exponent high_source_product by simp
      finally show ?thesis .
    qed
    have low_equality:
        "r * ?T powr beta * F powr (1 - beta) = r powr theta * F"
    proof -
      have "r * ?T powr beta * F powr (1 - beta) =
          (r * r powr (?gamma * beta)) *
            (F powr beta * F powr (1 - beta))"
        by (simp only: low_threshold_power mult.assoc mult.commute
            mult.left_commute)
      also have "... = r powr theta * F"
        using low_rate_product low_source_product by simp
      finally show ?thesis .
    qed
    show ?thesis
      by (rule exI[where x="?T"])
        (use threshold_positive high_equality low_equality in simp)
  qed
qed

theorem slp_interpolation_balancing_threshold:
  fixes p a b theta r F :: real
  assumes a_positive: "0 < a"
    and a_below_p: "a < p"
    and p_below_b: "p < b"
    and interpolation_identity:
      "1 / p = (1 - theta) / a + theta / b"
    and rate_positive: "0 < r"
    and size_nonnegative: "0 \<le> F"
  shows
    "\<exists>T>0.
      T powr (1 - p / a) * F powr (p / a) \<le> r powr theta * F
      \<and> r * T powr (1 - p / b) * F powr (p / b)
        \<le> r powr theta * F"
proof -
  have p_positive: "0 < p"
    using a_positive a_below_p by linarith
  have b_positive: "0 < b"
    using p_positive p_below_b by linarith
  have a_nonzero: "a \<noteq> 0"
    using a_positive by simp
  have p_nonzero: "p \<noteq> 0"
    using p_positive by simp
  have b_nonzero: "b \<noteq> 0"
    using b_positive by simp
  have a_not_b: "a \<noteq> b"
    using a_below_p p_below_b by linarith

  let ?alpha = "1 - p / a"
  let ?beta = "1 - p / b"
  have alpha_negative: "?alpha < 0"
  proof -
    have "1 < p / a"
      using a_positive a_below_p by (simp add: pos_less_divide_eq)
    then show ?thesis by linarith
  qed
  have beta_positive: "0 < ?beta"
  proof -
    have "p / b < 1"
      using b_positive p_below_b by (simp add: pos_divide_less_eq)
    then show ?thesis by linarith
  qed
  have beta_below_one: "?beta < 1"
    using p_positive b_positive by simp
  have denominator_positive: "0 < ?beta - ?alpha"
    using alpha_negative beta_positive by linarith
  have denominator_nonzero: "?beta - ?alpha \<noteq> 0"
    using denominator_positive by linarith

  have reciprocal_scaled:
      "1 = p * ((1 - theta) / a + theta / b)"
  proof -
    have "p * (1 / p) = p * ((1 - theta) / a + theta / b)"
      using interpolation_identity by (rule arg_cong[where f="\<lambda>x. p * x"])
    then show ?thesis
      using p_nonzero by simp
  qed
  have reciprocal_products:
      "1 = (p / a) * (1 - theta) + (p / b) * theta"
    using reciprocal_scaled by (simp add: divide_inverse algebra_simps)
  define x :: real where "x = p / a"
  define y :: real where "y = p / b"
  have reciprocal_xy: "1 = x * (1 - theta) + y * theta"
    using reciprocal_products by (simp only: x_def y_def)
  have reciprocal_xy_symmetric: "x * (1 - theta) + y * theta = 1"
    using reciprocal_xy by (rule sym)
  have theta_product_xy:
      "theta * ((1 - y) - (1 - x)) = - (1 - x)"
  proof -
    have "theta * ((1 - y) - (1 - x)) =
        - (x * (1 - theta) + y * theta) + x"
      by (simp add: algebra_simps)
    also have "... = - 1 + x"
      by (simp only: reciprocal_xy_symmetric)
    also have "... = - (1 - x)"
      by simp
    finally show ?thesis .
  qed
  have theta_product: "theta * (?beta - ?alpha) = - ?alpha"
    using theta_product_xy by (simp only: x_def y_def)
  have theta_as_ratio: "theta = - ?alpha / (?beta - ?alpha)"
    using theta_product denominator_nonzero a_nonzero p_nonzero b_nonzero
      a_not_b
    by (simp add: field_simps)

  note balanced = slp_two_power_balancing_threshold[
    OF alpha_negative beta_positive beta_below_one rate_positive
      size_nonnegative theta_as_ratio]
  show ?thesis
    using balanced by simp
qed

end
