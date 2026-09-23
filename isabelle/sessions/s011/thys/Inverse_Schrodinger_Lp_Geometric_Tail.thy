theory Inverse_Schrodinger_Lp_Geometric_Tail
  imports Inverse_Schrodinger_Lp_Tail_Power_Decay
begin

section \<open>One-sided geometric Neumann tails\<close>

text \<open>
  The manuscript tail beginning at index N is represented by the shifted
  series with term rho^(N+k).  This keeps the reindexing explicit and avoids
  attaching any convergence meaning to a set-indexed notation.
\<close>

definition slp_geometric_tail :: "real \<Rightarrow> nat \<Rightarrow> real" where
  "slp_geometric_tail rho N = (\<Sum>k. rho ^ (N + k))"

lemma slp_geometric_tail_summable:
  fixes rho :: real and N :: nat
  assumes rho_norm: "norm rho < 1"
  shows "summable (\<lambda>k. rho ^ (N + k))"
proof -
  have geometric: "summable (\<lambda>k. rho ^ k)"
    by (rule summable_geometric[OF rho_norm])
  have "summable (\<lambda>k. rho ^ N * rho ^ k)"
    by (rule summable_mult[OF geometric])
  then show ?thesis
    by (simp only: power_add)
qed

lemma slp_geometric_tail_identity:
  fixes rho :: real and N :: nat
  assumes rho_norm: "norm rho < 1"
  shows "slp_geometric_tail rho N = rho ^ N / (1 - rho)"
proof -
  have geometric: "summable (\<lambda>k. rho ^ k)"
    by (rule summable_geometric[OF rho_norm])
  have suminf_geometric_rho:
    "(\<Sum>k. rho ^ k) = 1 / (1 - rho)"
    by (rule suminf_geometric[OF rho_norm])
  have "slp_geometric_tail rho N = rho ^ N * (\<Sum>k. rho ^ k)"
    unfolding slp_geometric_tail_def
    by (simp only: power_add suminf_mult[OF geometric])
  then show ?thesis
    by (simp add: suminf_geometric_rho divide_inverse)
qed

theorem slp_geometric_tail_le_twice:
  fixes rho :: real and N :: nat
  assumes rho_nonnegative: "0 \<le> rho"
    and rho_half: "rho \<le> 1 / 2"
  shows "slp_geometric_tail rho N \<le> 2 * rho ^ N"
proof -
  have rho_norm: "norm rho < 1"
    using rho_nonnegative rho_half
    by (simp add: real_norm_def abs_of_nonneg; linarith)
  have denominator_positive: "0 < 1 - rho"
    using rho_half by linarith
  have inverse_bound: "1 / (1 - rho) \<le> 2"
  proof -
    have division_equivalence:
      "((1 :: real) / (1 - rho) \<le> 2) \<longleftrightarrow>
        (1 \<le> 2 * (1 - rho))"
      by (rule pos_divide_le_eq[OF denominator_positive])
    have half_equivalence:
      "(rho \<le> (1 :: real) / 2) \<longleftrightarrow> rho * 2 \<le> 1"
      by (rule pos_le_divide_eq; simp)
    have rho_twice: "rho * 2 \<le> 1"
      by (rule iffD1[OF half_equivalence rho_half])
    have polynomial_bound_expanded: "(1 :: real) \<le> 2 - rho * 2"
      using rho_twice by linarith
    have polynomial_bound: "(1 :: real) \<le> 2 * (1 - rho)"
      using polynomial_bound_expanded
      by (simp add: left_diff_distrib mult.commute)
    show ?thesis
      by (rule iffD2[OF division_equivalence polynomial_bound])
  qed
  have power_nonnegative: "0 \<le> rho ^ N"
    by (rule zero_le_power[OF rho_nonnegative])
  have tail_identity:
    "slp_geometric_tail rho N = rho ^ N * (1 / (1 - rho))"
    using slp_geometric_tail_identity[OF rho_norm, of N]
    by (simp add: divide_inverse)
  have scaled_inverse_bound:
    "rho ^ N * (1 / (1 - rho)) \<le> rho ^ N * 2"
    by (rule mult_left_mono[OF inverse_bound power_nonnegative])
  have "slp_geometric_tail rho N \<le> rho ^ N * 2"
    using tail_identity scaled_inverse_bound by linarith
  then show ?thesis
    by (simp add: mult.commute)
qed

corollary slp_geometric_tail_scaled_le:
  fixes C :: real
  assumes C_nonnegative: "0 \<le> C"
    and rho_nonnegative: "0 \<le> rho"
    and rho_half: "rho \<le> 1 / 2"
  shows "C * slp_geometric_tail rho N \<le> 2 * C * rho ^ N"
proof -
  have "C * slp_geometric_tail rho N \<le> C * (2 * rho ^ N)"
    by (rule mult_left_mono[OF
          slp_geometric_tail_le_twice[OF rho_nonnegative rho_half]
          C_nonnegative])
  then show ?thesis
    by (simp add: mult.assoc mult.commute mult.left_commute)
qed

end
