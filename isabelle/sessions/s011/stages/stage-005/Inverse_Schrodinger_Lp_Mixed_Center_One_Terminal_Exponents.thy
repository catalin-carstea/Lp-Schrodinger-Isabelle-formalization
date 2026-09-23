theory Inverse_Schrodinger_Lp_Mixed_Center_One_Terminal_Exponents
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_Weighted_Exponents"
begin

section \<open>Companion exponents for one-terminal mixed densities\<close>

definition slp_mixed_unit_branch_exponent :: "real \<Rightarrow> real" where
  "slp_mixed_unit_branch_exponent p = 2 * (p + 1) / (3 * p - 1)"

definition slp_mixed_unit_branch_holder_exponent :: "real \<Rightarrow> real" where
  "slp_mixed_unit_branch_holder_exponent p = 2 * (p + 1) / (3 - p)"

lemma slp_mixed_one_terminal_exponents:
  assumes p_lower: "1 < p"
    and p_upper: "p < 2"
  shows weighted_lower: "1 < slp_branch_power_exponent p"
    and weighted_upper: "slp_branch_power_exponent p < 2"
    and unit_lower: "1 < slp_mixed_unit_branch_exponent p"
    and unit_upper: "slp_mixed_unit_branch_exponent p < 2"
    and holder_lower: "1 < slp_mixed_unit_branch_holder_exponent p"
    and holder_conjugate:
      "1 / slp_mixed_unit_branch_exponent p +
        1 / slp_mixed_unit_branch_holder_exponent p = 1"
    and mixed_relation:
      "1 / slp_branch_power_exponent p +
        1 / slp_mixed_unit_branch_exponent p = 3 / 2"
proof -
  let ?D = "3 * p - 1"
  let ?H = "3 - p"
  have p_positive: "0 < p"
    using p_lower by linarith
  have p_plus_one_positive: "0 < p + 1"
    using p_positive by linarith
  have D_positive: "0 < ?D"
    using p_lower by linarith
  have H_positive: "0 < ?H"
    using p_upper by linarith
  have p_plus_one_nonzero: "p + 1 \<noteq> 0"
    using p_plus_one_positive by simp
  have D_nonzero: "?D \<noteq> 0"
    using D_positive by simp
  have H_nonzero: "?H \<noteq> 0"
    using H_positive by simp
  show "1 < slp_branch_power_exponent p"
    using slp_branch_weighted_exponents(1)[OF p_lower p_upper] .
  show "slp_branch_power_exponent p < 2"
    using slp_branch_weighted_exponents(2)[OF p_lower p_upper] p_upper
    by linarith
  show "1 < slp_mixed_unit_branch_exponent p"
    unfolding slp_mixed_unit_branch_exponent_def
    using D_positive p_upper
    by (simp add: less_divide_eq)
  show "slp_mixed_unit_branch_exponent p < 2"
    unfolding slp_mixed_unit_branch_exponent_def
    using D_positive p_lower
    by (simp add: divide_less_eq)
  show "1 < slp_mixed_unit_branch_holder_exponent p"
    unfolding slp_mixed_unit_branch_holder_exponent_def
    using H_positive p_lower
    by (simp add: less_divide_eq)
  show "1 / slp_mixed_unit_branch_exponent p +
      1 / slp_mixed_unit_branch_holder_exponent p = 1"
  proof -
    have numerator_sum: "?D + ?H = 2 * (p + 1)"
      by ring
    show ?thesis
    unfolding slp_mixed_unit_branch_exponent_def
      slp_mixed_unit_branch_holder_exponent_def
      using p_plus_one_nonzero D_nonzero H_nonzero numerator_sum
      by (simp add: add_divide_distrib [symmetric])
  qed
  show "1 / slp_branch_power_exponent p +
      1 / slp_mixed_unit_branch_exponent p = 3 / 2"
  proof -
    have numerator_sum: "4 + ?D = 3 * (p + 1)"
      by ring
    have inverse_weight:
        "1 / slp_branch_power_exponent p = 2 / (p + 1)"
      unfolding slp_branch_power_exponent_def
      using p_plus_one_nonzero by simp
    have inverse_unit:
        "1 / slp_mixed_unit_branch_exponent p =
          ?D / (2 * (p + 1))"
      unfolding slp_mixed_unit_branch_exponent_def
      using p_plus_one_nonzero D_nonzero by simp
    have first_scaled:
        "2 / (p + 1) = 4 / (2 * (p + 1))"
      apply (subst frac_eq_eq)
      using p_plus_one_nonzero apply simp
      using p_plus_one_nonzero apply simp
      by ring
    have common_denominator:
        "4 / (2 * (p + 1)) + ?D / (2 * (p + 1)) =
          (4 + ?D) / (2 * (p + 1))"
      by (rule add_divide_distrib [symmetric])
    have normalized:
        "(4 + ?D) / (2 * (p + 1)) = 3 / 2"
      apply (subst frac_eq_eq)
      using p_plus_one_nonzero apply simp
      apply simp
      using numerator_sum by ring
    show ?thesis
      by (simp only: inverse_weight inverse_unit first_scaled
            common_denominator normalized)
  qed
qed

end
