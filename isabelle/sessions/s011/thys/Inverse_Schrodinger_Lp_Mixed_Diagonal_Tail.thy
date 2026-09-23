theory Inverse_Schrodinger_Lp_Mixed_Diagonal_Tail
  imports Inverse_Schrodinger_Lp_Weighted_Geometric_Tail
begin

section \<open>Mixed tails grouped by total order\<close>

definition slp_mixed_diagonal_term :: "real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real" where
  "slp_mixed_diagonal_term rho rho_tilde n =
    (\<Sum>j<Suc n. rho ^ j * rho_tilde ^ (n - j))"

definition slp_mixed_diagonal_tail ::
    "real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real" where
  "slp_mixed_diagonal_tail rho rho_tilde N =
    (\<Sum>k. slp_mixed_diagonal_term rho rho_tilde (N + k))"

lemma slp_mixed_diagonal_term_nonnegative:
  assumes rho_nonnegative: "0 \<le> rho"
    and rho_tilde_nonnegative: "0 \<le> rho_tilde"
  shows "0 \<le> slp_mixed_diagonal_term rho rho_tilde n"
  unfolding slp_mixed_diagonal_term_def
  using rho_nonnegative rho_tilde_nonnegative
  by (intro sum_nonneg) simp

lemma slp_mixed_diagonal_term_le_max:
  assumes rho_nonnegative: "0 \<le> rho"
    and rho_tilde_nonnegative: "0 \<le> rho_tilde"
  shows
    "slp_mixed_diagonal_term rho rho_tilde n \<le>
      real (n + 1) * max rho rho_tilde ^ n"
proof -
  let ?m = "max rho rho_tilde"
  have rho_le: "rho \<le> ?m"
    by (rule max.cobounded1)
  have rho_tilde_le: "rho_tilde \<le> ?m"
    by (rule max.cobounded2)
  have each_term:
    "rho ^ j * rho_tilde ^ (n - j) \<le> ?m ^ n"
    if j_range: "j \<in> {..<Suc n}" for j
  proof -
    have j_le: "j \<le> n"
      using j_range by simp
    have first_power: "rho ^ j \<le> ?m ^ j"
      by (rule power_mono[OF rho_le rho_nonnegative])
    have second_power: "rho_tilde ^ (n - j) \<le> ?m ^ (n - j)"
      by (rule power_mono[OF rho_tilde_le rho_tilde_nonnegative])
    have product_bound:
      "rho ^ j * rho_tilde ^ (n - j) \<le>
        ?m ^ j * ?m ^ (n - j)"
      by (rule mult_mono[OF first_power second_power])
        (use rho_nonnegative rho_tilde_nonnegative in simp_all)
    have power_identity: "?m ^ j * ?m ^ (n - j) = ?m ^ n"
      using j_le by (simp add: power_add [symmetric])
    show ?thesis
      using product_bound power_identity by simp
  qed
  have finite_bound:
    "(\<Sum>j<Suc n. rho ^ j * rho_tilde ^ (n - j)) \<le>
      real (card {..<Suc n}) * ?m ^ n"
    by (rule sum_bounded_above[OF each_term])
  show ?thesis
    unfolding slp_mixed_diagonal_term_def
    using finite_bound by simp
qed

lemma slp_weighted_shifted_summable:
  fixes rho :: real
  assumes rho_nonnegative: "0 \<le> rho"
    and rho_half: "rho \<le> 1 / 2"
  shows "summable (\<lambda>k. real (N + k + 1) * rho ^ (N + k))"
proof -
  have inner:
    "summable (\<lambda>k. real (N + k + 1) * rho ^ k)"
    by (rule slp_weighted_inner_summable[
          OF rho_nonnegative rho_half])
  have scaled:
    "summable
      (\<lambda>k. rho ^ N * (real (N + k + 1) * rho ^ k))"
    by (rule summable_mult[OF inner])
  have eventual_identity:
    "eventually
      (\<lambda>k.
        real (N + k + 1) * rho ^ (N + k) =
          rho ^ N * (real (N + k + 1) * rho ^ k))
      sequentially"
    by (simp add: power_add mult.assoc mult.commute mult.left_commute)
  from summable_cong[OF eventual_identity] scaled show ?thesis
    by blast
qed

lemma slp_mixed_diagonal_shifted_summable:
  assumes rho_nonnegative: "0 \<le> rho"
    and rho_tilde_nonnegative: "0 \<le> rho_tilde"
    and rho_half: "rho \<le> 1 / 2"
    and rho_tilde_half: "rho_tilde \<le> 1 / 2"
  shows
    "summable
      (\<lambda>k. slp_mixed_diagonal_term rho rho_tilde (N + k))"
proof -
  let ?m = "max rho rho_tilde"
  have max_nonnegative: "0 \<le> ?m"
    using rho_nonnegative by simp
  have max_half: "?m \<le> 1 / 2"
    using rho_half rho_tilde_half by simp
  have weighted_summable:
    "summable (\<lambda>k. real (N + k + 1) * ?m ^ (N + k))"
    by (rule slp_weighted_shifted_summable[
          OF max_nonnegative max_half])
  show ?thesis
  proof (rule summable_comparison_test'[OF weighted_summable, where N = 0])
    fix k :: nat
    assume "0 \<le> k"
    have diagonal_nonnegative:
      "0 \<le> slp_mixed_diagonal_term rho rho_tilde (N + k)"
      by (rule slp_mixed_diagonal_term_nonnegative[
            OF rho_nonnegative rho_tilde_nonnegative])
    have diagonal_bound:
      "slp_mixed_diagonal_term rho rho_tilde (N + k) \<le>
        real (N + k + 1) * ?m ^ (N + k)"
      by (rule slp_mixed_diagonal_term_le_max[
            OF rho_nonnegative rho_tilde_nonnegative])
    show
      "norm (slp_mixed_diagonal_term rho rho_tilde (N + k)) \<le>
        real (N + k + 1) * ?m ^ (N + k)"
      using diagonal_nonnegative diagonal_bound by simp
  qed
qed

theorem slp_mixed_diagonal_tail_le_weighted:
  assumes rho_nonnegative: "0 \<le> rho"
    and rho_tilde_nonnegative: "0 \<le> rho_tilde"
    and rho_half: "rho \<le> 1 / 2"
    and rho_tilde_half: "rho_tilde \<le> 1 / 2"
  shows
    "slp_mixed_diagonal_tail rho rho_tilde N \<le>
      slp_weighted_geometric_tail (max rho rho_tilde) N"
proof -
  let ?m = "max rho rho_tilde"
  have max_nonnegative: "0 \<le> ?m"
    using rho_nonnegative by simp
  have max_half: "?m \<le> 1 / 2"
    using rho_half rho_tilde_half by simp
  have mixed_summable:
    "summable
      (\<lambda>k. slp_mixed_diagonal_term rho rho_tilde (N + k))"
    by (rule slp_mixed_diagonal_shifted_summable[
          OF rho_nonnegative rho_tilde_nonnegative rho_half rho_tilde_half])
  have weighted_summable:
    "summable (\<lambda>k. real (N + k + 1) * ?m ^ (N + k))"
    by (rule slp_weighted_shifted_summable[
          OF max_nonnegative max_half])
  show ?thesis
    unfolding slp_mixed_diagonal_tail_def
      slp_weighted_geometric_tail_def
    by (rule suminf_le[
          OF slp_mixed_diagonal_term_le_max[
            OF rho_nonnegative rho_tilde_nonnegative]
          mixed_summable weighted_summable])
qed

corollary slp_mixed_diagonal_tail_le_constant:
  assumes rho_nonnegative: "0 \<le> rho"
    and rho_tilde_nonnegative: "0 \<le> rho_tilde"
    and rho_half: "rho \<le> 1 / 2"
    and rho_tilde_half: "rho_tilde \<le> 1 / 2"
  shows
    "slp_mixed_diagonal_tail rho rho_tilde N \<le>
      slp_weighted_tail_constant N * max rho rho_tilde ^ N"
proof -
  let ?m = "max rho rho_tilde"
  have first:
    "slp_mixed_diagonal_tail rho rho_tilde N \<le>
      slp_weighted_geometric_tail ?m N"
    by (rule slp_mixed_diagonal_tail_le_weighted[
          OF rho_nonnegative rho_tilde_nonnegative rho_half rho_tilde_half])
  have max_nonnegative: "0 \<le> ?m"
    using rho_nonnegative by simp
  have max_half: "?m \<le> 1 / 2"
    using rho_half rho_tilde_half by simp
  have second:
    "slp_weighted_geometric_tail ?m N \<le>
      slp_weighted_tail_constant N * ?m ^ N"
    by (rule slp_weighted_geometric_tail_le[
          OF max_nonnegative max_half])
  show ?thesis
    using first second by (rule order_trans)
qed

end
