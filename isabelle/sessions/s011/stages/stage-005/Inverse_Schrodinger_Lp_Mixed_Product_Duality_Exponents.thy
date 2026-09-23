theory Inverse_Schrodinger_Lp_Mixed_Product_Duality_Exponents
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_005.Inverse_Schrodinger_Lp_Mixed_Center_Density_Membership_Clauses"
begin

section \<open>Duality exponents for the mixed product error\<close>

definition slp_mixed_product_exponent :: "real \<Rightarrow> real" where
  "slp_mixed_product_exponent p = aim_hls_target_exponent p / 2"

definition slp_mixed_product_dual_exponent :: "real \<Rightarrow> real" where
  "slp_mixed_product_dual_exponent p = p / (2 * (p - 1))"

lemma slp_mixed_product_duality_exponents:
  assumes p_lower: "1 < p"
    and p_upper: "p < 2"
  shows product_value:
      "slp_mixed_product_exponent p = p / (2 - p)"
    and product_lower: "1 < slp_mixed_product_exponent p"
    and dual_lower: "1 < slp_mixed_product_dual_exponent p"
    and conjugate:
      "1 / slp_mixed_product_exponent p +
        1 / slp_mixed_product_dual_exponent p = 1"
proof -
  have p_positive: "0 < p" using p_lower by linarith
  have product_denominator_positive: "0 < 2 - p" using p_upper by linarith
  have dual_denominator_positive: "0 < 2 * (p - 1)"
    using p_lower by simp
  have p_nonzero: "p \<noteq> 0" using p_positive by simp
  have product_denominator_nonzero: "2 - p \<noteq> 0"
    using product_denominator_positive by simp
  have dual_denominator_nonzero: "2 * (p - 1) \<noteq> 0"
    using dual_denominator_positive by simp
  have product_value:
      "slp_mixed_product_exponent p = p / (2 - p)"
  proof -
    have cancellation:
        "(2 * p / (2 - p)) / 2 = p / (2 - p)"
    proof -
      have "(2 * p / (2 - p)) / 2 =
          (2 * p) / ((2 - p) * 2)"
        by (rule divide_divide_eq_left)
      also have "... = (2 * p) / (2 * (2 - p))"
        by (simp only: mult.commute)
      also have "... = p / (2 - p)"
        by (rule nonzero_mult_divide_mult_cancel_left, simp)
      finally show ?thesis .
    qed
    show ?thesis
      unfolding slp_mixed_product_exponent_def aim_hls_target_exponent_def
      by (rule cancellation)
  qed
  show "slp_mixed_product_exponent p = p / (2 - p)"
    by (rule product_value)
  show "1 < slp_mixed_product_exponent p"
    unfolding product_value
    using product_denominator_positive p_lower
    by (simp add: less_divide_eq)
  show "1 < slp_mixed_product_dual_exponent p"
    unfolding slp_mixed_product_dual_exponent_def
    using dual_denominator_positive p_upper
    by (simp add: less_divide_eq)
  show "1 / slp_mixed_product_exponent p +
      1 / slp_mixed_product_dual_exponent p = 1"
  proof -
    have inverse_product:
        "1 / slp_mixed_product_exponent p = (2 - p) / p"
      unfolding product_value
      using p_nonzero product_denominator_nonzero by simp
    have inverse_dual:
        "1 / slp_mixed_product_dual_exponent p =
          2 * (p - 1) / p"
      unfolding slp_mixed_product_dual_exponent_def
      using p_nonzero dual_denominator_nonzero by simp
    have numerator_sum: "(2 - p) + 2 * (p - 1) = p"
      by (simp add: algebra_simps)
    show ?thesis
      apply (simp only: inverse_product inverse_dual
        add_divide_distrib [symmetric])
      apply (subst numerator_sum)
      using p_nonzero by simp
  qed
qed

end
