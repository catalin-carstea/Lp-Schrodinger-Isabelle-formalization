theory Inverse_Schrodinger_Lp_Mixed_Center_Unweighted_Exponents
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_005.Inverse_Schrodinger_Lp_Mixed_Center_Density_Endpoint_Clauses"
begin

section \<open>Finite-target exponents for unweighted mixed densities\<close>

definition slp_mixed_unweighted_branch_exponent :: "real \<Rightarrow> real" where
  "slp_mixed_unweighted_branch_exponent t = 2 * t / (t + 1)"

definition slp_mixed_unweighted_branch_holder_exponent ::
    "real \<Rightarrow> real" where
  "slp_mixed_unweighted_branch_holder_exponent t = 2 * t / (t - 1)"

lemma slp_mixed_unweighted_finite_target_exponents:
  assumes t_lower: "1 < t"
  shows branch_lower: "1 < slp_mixed_unweighted_branch_exponent t"
    and branch_upper: "slp_mixed_unweighted_branch_exponent t < 2"
    and holder_lower:
      "1 < slp_mixed_unweighted_branch_holder_exponent t"
    and holder_conjugate:
      "1 / slp_mixed_unweighted_branch_exponent t +
        1 / slp_mixed_unweighted_branch_holder_exponent t = 1"
    and young_relation:
      "1 + 1 / t = 1 / slp_mixed_unweighted_branch_exponent t +
        1 / slp_mixed_unweighted_branch_exponent t"
proof -
  have t_positive: "0 < t"
    using t_lower by linarith
  have t_plus_one_positive: "0 < t + 1"
    using t_positive by linarith
  have t_minus_one_positive: "0 < t - 1"
    using t_lower by linarith
  have t_nonzero: "t \<noteq> 0"
    using t_positive by simp
  have t_plus_one_nonzero: "t + 1 \<noteq> 0"
    using t_plus_one_positive by simp
  have t_minus_one_nonzero: "t - 1 \<noteq> 0"
    using t_minus_one_positive by simp
  show "1 < slp_mixed_unweighted_branch_exponent t"
    unfolding slp_mixed_unweighted_branch_exponent_def
    using t_plus_one_positive t_lower
    by (simp add: less_divide_eq)
  show "slp_mixed_unweighted_branch_exponent t < 2"
    unfolding slp_mixed_unweighted_branch_exponent_def
    using t_plus_one_positive
    by (simp add: divide_less_eq)
  show "1 < slp_mixed_unweighted_branch_holder_exponent t"
    unfolding slp_mixed_unweighted_branch_holder_exponent_def
    using t_minus_one_positive t_positive
    by (simp add: less_divide_eq)
  show "1 / slp_mixed_unweighted_branch_exponent t +
      1 / slp_mixed_unweighted_branch_holder_exponent t = 1"
  proof -
    have inverse_branch:
        "1 / slp_mixed_unweighted_branch_exponent t =
          (t + 1) / (2 * t)"
      unfolding slp_mixed_unweighted_branch_exponent_def
      using t_nonzero t_plus_one_nonzero by simp
    have inverse_holder:
        "1 / slp_mixed_unweighted_branch_holder_exponent t =
          (t - 1) / (2 * t)"
      unfolding slp_mixed_unweighted_branch_holder_exponent_def
      using t_nonzero t_minus_one_nonzero by simp
    have numerator_sum: "(t + 1) + (t - 1) = 2 * t"
      by ring
    have common_denominator:
        "(t + 1) / (2 * t) + (t - 1) / (2 * t) =
          ((t + 1) + (t - 1)) / (2 * t)"
      by (rule add_divide_distrib [symmetric])
    have normalized: "((t + 1) + (t - 1)) / (2 * t) = 1"
      using numerator_sum t_nonzero by simp
    show ?thesis
      by (simp only: inverse_branch inverse_holder common_denominator normalized)
  qed
  show "1 + 1 / t = 1 / slp_mixed_unweighted_branch_exponent t +
      1 / slp_mixed_unweighted_branch_exponent t"
  proof -
    have inverse_branch:
        "1 / slp_mixed_unweighted_branch_exponent t =
          (t + 1) / (2 * t)"
      unfolding slp_mixed_unweighted_branch_exponent_def
      using t_nonzero t_plus_one_nonzero by simp
    have one_fraction: "(1 :: real) = t / t"
      using t_nonzero by simp
    have left_normalized: "1 + 1 / t = (t + 1) / t"
      by (simp only: one_fraction add_divide_distrib [symmetric])
    have right_common:
        "(t + 1) / (2 * t) + (t + 1) / (2 * t) =
          ((t + 1) + (t + 1)) / (2 * t)"
      by (rule add_divide_distrib [symmetric])
    have numerator_double: "(t + 1) + (t + 1) = 2 * (t + 1)"
      by ring
    have scale_cancel: "2 * (t + 1) / (2 * t) = (t + 1) / t"
      apply (subst frac_eq_eq)
      using t_nonzero apply simp
      using t_nonzero apply simp
      by ring
    show ?thesis
      by (simp only: inverse_branch left_normalized right_common
            numerator_double scale_cancel)
  qed
qed

end
