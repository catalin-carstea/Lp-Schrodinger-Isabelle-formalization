theory Inverse_Schrodinger_Lp_Born_Weighted_Exponents
  imports
    Inverse_Schrodinger_Lp_Born_All_Order_Terminal_Lp
    "HOL-Decision_Procs.Commutative_Ring"
begin

section \<open>An explicit weighted-branch exponent tuple\<close>

definition slp_branch_power_exponent :: "real \<Rightarrow> real" where
  "slp_branch_power_exponent p = (p + 1) / 2"

definition slp_branch_holder_exponent :: "real \<Rightarrow> real" where
  "slp_branch_holder_exponent p = (p + 1) / (p - 1)"

definition slp_branch_terminal_exponent :: "real \<Rightarrow> real" where
  "slp_branch_terminal_exponent p = 2 * p / (2 - p)"

definition slp_branch_kernel_exponent :: "real \<Rightarrow> real" where
  "slp_branch_kernel_exponent p =
    2 * p * (p + 1) / (p ^ 2 + 3 * p - 2)"

lemma slp_branch_weighted_exponents:
  assumes p_lower: "1 < p"
    and p_upper: "p < 2"
  shows power_lower: "1 < slp_branch_power_exponent p"
    and power_upper: "slp_branch_power_exponent p < p"
    and holder_lower: "1 < slp_branch_holder_exponent p"
    and holder_conjugate:
      "1 / slp_branch_power_exponent p +
        1 / slp_branch_holder_exponent p = 1"
    and kernel_lower: "1 < slp_branch_kernel_exponent p"
    and kernel_upper: "slp_branch_kernel_exponent p < 2"
    and kernel_scale:
      "1 < slp_branch_kernel_exponent p /
        slp_branch_power_exponent p"
    and terminal_scale:
      "1 < slp_branch_terminal_exponent p /
        slp_branch_power_exponent p"
    and scaled_conjugate:
      "1 /
          (slp_branch_kernel_exponent p /
            slp_branch_power_exponent p) +
        1 /
          (slp_branch_terminal_exponent p /
            slp_branch_power_exponent p) = 1"
proof -
  let ?D = "p ^ 2 + 3 * p - 2"
  have p_positive: "0 < p"
    using p_lower by linarith
  have p_minus_one_positive: "0 < p - 1"
    using p_lower by linarith
  have two_minus_p_positive: "0 < 2 - p"
    using p_upper by linarith
  have p_plus_one_positive: "0 < p + 1"
    using p_positive by linarith
  have p_times_gap_positive: "0 < p * (p - 1)"
    using p_positive p_minus_one_positive by simp
  have endpoint_product_positive: "0 < (2 - p) * (p + 1)"
    using two_minus_p_positive p_plus_one_positive by simp
  have D_positive: "0 < ?D"
  proof -
    have two_p_minus_one_positive: "0 < 2 * p - 1"
      using p_lower by linarith
    have "0 < p * (p - 1) + 2 * (2 * p - 1)"
      using p_times_gap_positive two_p_minus_one_positive by simp
    also have "p * (p - 1) + 2 * (2 * p - 1) = ?D"
      by ring
    finally show ?thesis .
  qed
  have p_nonzero: "p \<noteq> 0"
    using p_positive by simp
  have p_minus_one_nonzero: "p - 1 \<noteq> 0"
    using p_minus_one_positive by simp
  have p_plus_one_nonzero: "p + 1 \<noteq> 0"
    using p_plus_one_positive by simp
  have two_minus_p_nonzero: "2 - p \<noteq> 0"
    using two_minus_p_positive by simp
  have D_nonzero: "?D \<noteq> 0"
    using D_positive by simp
  show "1 < slp_branch_power_exponent p"
    unfolding slp_branch_power_exponent_def
    using p_lower by (simp add: less_divide_eq)
  show "slp_branch_power_exponent p < p"
    unfolding slp_branch_power_exponent_def
    using p_lower by (simp add: divide_less_eq)
  show "1 < slp_branch_holder_exponent p"
    unfolding slp_branch_holder_exponent_def
    using p_minus_one_positive
    by (simp add: less_divide_eq)
  show "1 / slp_branch_power_exponent p +
      1 / slp_branch_holder_exponent p = 1"
    unfolding slp_branch_power_exponent_def
      slp_branch_holder_exponent_def
    using p_plus_one_nonzero
    by (simp add: add_divide_distrib [symmetric])
  show "1 < slp_branch_kernel_exponent p"
  proof -
    have "0 < p * (p - 1) + 2"
      using p_times_gap_positive by simp
    also have "p * (p - 1) + 2 =
        2 * p * (p + 1) - ?D"
      by ring
    finally have "?D < 2 * p * (p + 1)"
      by linarith
    with D_positive show ?thesis
      unfolding slp_branch_kernel_exponent_def
      by (simp add: less_divide_eq)
  qed
  show "slp_branch_kernel_exponent p < 2"
  proof -
    have "0 < 4 * (p - 1)"
      using p_minus_one_positive by simp
    also have "4 * (p - 1) =
        2 * ?D - 2 * p * (p + 1)"
      by ring
    finally have "2 * p * (p + 1) < 2 * ?D"
      by linarith
    with D_positive show ?thesis
      unfolding slp_branch_kernel_exponent_def
      by (simp add: divide_less_eq)
  qed
  have kernel_over_power:
      "slp_branch_kernel_exponent p /
          slp_branch_power_exponent p =
        4 * p / ?D"
    unfolding slp_branch_kernel_exponent_def
      slp_branch_power_exponent_def
    using p_plus_one_nonzero D_nonzero
    by (simp add: divide_divide_times_eq)
  show "1 < slp_branch_kernel_exponent p /
      slp_branch_power_exponent p"
  proof -
    have "(2 - p) * (p + 1) = 4 * p - ?D"
      by ring
    with endpoint_product_positive have "?D < 4 * p"
      by linarith
    with D_positive show ?thesis
      unfolding kernel_over_power
      by (simp add: less_divide_eq)
  qed
  have terminal_over_power:
      "slp_branch_terminal_exponent p /
          slp_branch_power_exponent p =
        4 * p / ((2 - p) * (p + 1))"
    unfolding slp_branch_terminal_exponent_def
      slp_branch_power_exponent_def
    using p_plus_one_nonzero two_minus_p_nonzero
    by (simp add: divide_divide_times_eq)
  show "1 < slp_branch_terminal_exponent p /
      slp_branch_power_exponent p"
  proof -
    have "?D = 4 * p - (2 - p) * (p + 1)"
      by ring
    with D_positive have "(2 - p) * (p + 1) < 4 * p"
      by linarith
    with endpoint_product_positive show ?thesis
      unfolding terminal_over_power
      by (simp add: less_divide_eq)
  qed
  show "1 /
        (slp_branch_kernel_exponent p /
          slp_branch_power_exponent p) +
      1 /
        (slp_branch_terminal_exponent p /
          slp_branch_power_exponent p) = 1"
  proof -
    have numerator_sum:
        "?D + (2 - p) * (p + 1) = 4 * p"
      by ring
    show ?thesis
      unfolding kernel_over_power terminal_over_power
      using p_nonzero numerator_sum
      by (simp add: add_divide_distrib [symmetric])
  qed
qed

end
