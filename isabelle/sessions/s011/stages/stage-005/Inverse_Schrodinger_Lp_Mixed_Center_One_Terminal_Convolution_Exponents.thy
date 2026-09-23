theory Inverse_Schrodinger_Lp_Mixed_Center_One_Terminal_Convolution_Exponents
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_005.Inverse_Schrodinger_Lp_Mixed_Center_One_Terminal_Exponents"
begin

section \<open>Split exponents for one-terminal mixed convolution\<close>

definition slp_mixed_weight_split_exponent :: "real \<Rightarrow> real" where
  "slp_mixed_weight_split_exponent p = (p + 1) / (3 - p)"

definition slp_mixed_unit_split_exponent :: "real \<Rightarrow> real" where
  "slp_mixed_unit_split_exponent p = (p + 1) / (2 * (p - 1))"

lemma slp_mixed_one_terminal_convolution_exponents:
  assumes p_lower: "1 < p"
    and p_upper: "p < 2"
  shows weight_split_lower: "1 < slp_mixed_weight_split_exponent p"
    and unit_split_lower: "1 < slp_mixed_unit_split_exponent p"
    and split_conjugate:
      "1 / slp_mixed_weight_split_exponent p +
        1 / slp_mixed_unit_split_exponent p = 1"
    and weight_scale:
      "(2 - slp_branch_power_exponent p) *
        slp_mixed_weight_split_exponent p =
          slp_branch_power_exponent p"
    and unit_scale:
      "(2 - slp_mixed_unit_branch_exponent p) *
        slp_mixed_unit_split_exponent p =
          slp_mixed_unit_branch_exponent p"
proof -
  have p_plus_one_positive: "0 < p + 1"
    using p_lower by linarith
  have weight_denominator_positive: "0 < 3 - p"
    using p_upper by linarith
  have unit_denominator_positive: "0 < 2 * (p - 1)"
    using p_lower by simp
  have p_plus_one_nonzero: "p + 1 \<noteq> 0"
    using p_plus_one_positive by simp
  have weight_denominator_nonzero: "3 - p \<noteq> 0"
    using weight_denominator_positive by simp
  have unit_denominator_nonzero: "2 * (p - 1) \<noteq> 0"
    using unit_denominator_positive by simp
  have branch_denominator_nonzero: "3 * p - 1 \<noteq> 0"
    using p_lower by linarith
  show "1 < slp_mixed_weight_split_exponent p"
    unfolding slp_mixed_weight_split_exponent_def
    using weight_denominator_positive p_lower
    by (simp add: less_divide_eq)
  show "1 < slp_mixed_unit_split_exponent p"
    unfolding slp_mixed_unit_split_exponent_def
    using unit_denominator_positive p_upper
    by (simp add: less_divide_eq)
  show "1 / slp_mixed_weight_split_exponent p +
      1 / slp_mixed_unit_split_exponent p = 1"
  proof -
    have inverse_weight:
        "1 / slp_mixed_weight_split_exponent p =
          (3 - p) / (p + 1)"
      unfolding slp_mixed_weight_split_exponent_def
      using p_plus_one_nonzero weight_denominator_nonzero by simp
    have inverse_unit:
        "1 / slp_mixed_unit_split_exponent p =
          2 * (p - 1) / (p + 1)"
      unfolding slp_mixed_unit_split_exponent_def
      using p_plus_one_nonzero unit_denominator_nonzero by simp
    have numerator_sum: "(3 - p) + 2 * (p - 1) = p + 1"
      by (simp add: algebra_simps)
    show ?thesis
      apply (simp only: inverse_weight inverse_unit
        add_divide_distrib [symmetric] p_plus_one_nonzero divide_self)
      apply (subst numerator_sum)
      using p_plus_one_nonzero by simp
  qed
  show "(2 - slp_branch_power_exponent p) *
      slp_mixed_weight_split_exponent p =
        slp_branch_power_exponent p"
  proof -
    have gap:
        "2 - slp_branch_power_exponent p = (3 - p) / 2"
      unfolding slp_branch_power_exponent_def
      by (simp add: algebra_simps)
    have cancel:
        "(3 - p) * slp_mixed_weight_split_exponent p = p + 1"
      unfolding slp_mixed_weight_split_exponent_def
      using weight_denominator_nonzero by simp
    have rearranged:
        "(2 - slp_branch_power_exponent p) *
          slp_mixed_weight_split_exponent p =
          ((3 - p) * slp_mixed_weight_split_exponent p) / 2"
      by (simp only: gap divide_inverse mult_ac)
    have reduced:
        "(2 - slp_branch_power_exponent p) *
          slp_mixed_weight_split_exponent p = (p + 1) / 2"
      using rearranged by (simp only: cancel)
    show ?thesis
      using reduced by (simp only: slp_branch_power_exponent_def)
  qed
  show "(2 - slp_mixed_unit_branch_exponent p) *
      slp_mixed_unit_split_exponent p =
        slp_mixed_unit_branch_exponent p"
  proof -
    have two_fraction:
        "2 = 2 * (3 * p - 1) / (3 * p - 1)"
      by (rule nonzero_eq_divide_eq[OF branch_denominator_nonzero, THEN iffD2])
        simp
    have gap:
        "2 - slp_mixed_unit_branch_exponent p =
          2 * (2 * (p - 1)) / (3 * p - 1)"
    proof -
      have numerator:
          "2 * (3 * p - 1) - 2 * (p + 1) = 2 * (2 * (p - 1))"
        by (simp add: algebra_simps)
      show ?thesis
        unfolding slp_mixed_unit_branch_exponent_def
        apply (subst two_fraction)
        by (simp only: diff_divide_distrib [symmetric] numerator)
    qed
    have cancel:
        "(2 * (p - 1)) * slp_mixed_unit_split_exponent p = p + 1"
      unfolding slp_mixed_unit_split_exponent_def
      using unit_denominator_nonzero by simp
    have rearranged:
        "(2 - slp_mixed_unit_branch_exponent p) *
          slp_mixed_unit_split_exponent p =
          2 * ((2 * (p - 1)) * slp_mixed_unit_split_exponent p) /
            (3 * p - 1)"
      by (simp only: gap divide_inverse mult_ac)
    have reduced:
        "(2 - slp_mixed_unit_branch_exponent p) *
          slp_mixed_unit_split_exponent p =
            2 * (p + 1) / (3 * p - 1)"
      using rearranged by (simp only: cancel)
    show ?thesis
      using reduced by (simp only: slp_mixed_unit_branch_exponent_def)
  qed
qed

end
