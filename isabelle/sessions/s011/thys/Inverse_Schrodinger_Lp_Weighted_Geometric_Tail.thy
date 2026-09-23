theory Inverse_Schrodinger_Lp_Weighted_Geometric_Tail
  imports Inverse_Schrodinger_Lp_Geometric_Tail
begin

section \<open>Weighted geometric tails for mixed Neumann terms\<close>

definition slp_weighted_geometric_tail ::
    "real \<Rightarrow> nat \<Rightarrow> real" where
  "slp_weighted_geometric_tail rho N =
    (\<Sum>k. real (N + k + 1) * rho ^ (N + k))"

definition slp_weighted_tail_constant :: "nat \<Rightarrow> real" where
  "slp_weighted_tail_constant N =
    (\<Sum>k. real (N + k + 1) * ((1 / 2 :: real) ^ k))"

lemma slp_summable_suc_times_power:
  fixes rho :: real
  assumes rho_norm: "norm rho < 1"
  shows "summable (\<lambda>k. real (Suc k) * rho ^ k)"
proof -
  have differentiated:
    "summable (\<lambda>k. diffs (\<lambda>_. (1 :: real)) k * rho ^ k)"
  proof (rule termdiff_converges[where K = 1])
    show "norm rho < 1"
      by (rule rho_norm)
    show "summable (\<lambda>n. (1 :: real) * x ^ n)"
      if "norm x < 1" for x :: real
      using summable_geometric[OF that] by simp
  qed
  then show ?thesis
    by (simp add: diffs_def)
qed

lemma slp_weighted_half_series_summable:
  "summable
    (\<lambda>k. real (N + k + 1) * ((1 / 2 :: real) ^ k))"
proof -
  have geometric_half:
    "summable (\<lambda>k. (1 / 2 :: real) ^ k)"
    by (rule summable_geometric) simp
  have constant_part:
    "summable (\<lambda>k. real N * ((1 / 2 :: real) ^ k))"
    by (rule summable_mult[OF geometric_half])
  have successor_part:
    "summable (\<lambda>k. real (Suc k) * ((1 / 2 :: real) ^ k))"
    by (rule slp_summable_suc_times_power) simp
  have combined:
    "summable
      (\<lambda>k. real N * ((1 / 2 :: real) ^ k) +
        real (Suc k) * ((1 / 2 :: real) ^ k))"
    by (rule summable_add[OF constant_part successor_part])
  have eventual_identity:
    "eventually
      (\<lambda>k.
        real (N + k + 1) * ((1 / 2 :: real) ^ k) =
        real N * ((1 / 2 :: real) ^ k) +
          real (Suc k) * ((1 / 2 :: real) ^ k))
      sequentially"
    by (simp add: algebra_simps)
  from summable_cong[OF eventual_identity] combined show ?thesis
    by blast
qed

lemma slp_weighted_tail_constant_nonnegative:
  "0 \<le> slp_weighted_tail_constant N"
  unfolding slp_weighted_tail_constant_def
  by (rule suminf_nonneg[OF slp_weighted_half_series_summable]) simp

lemma slp_weighted_inner_term_le_half:
  fixes rho :: real
  assumes rho_nonnegative: "0 \<le> rho"
    and rho_half: "rho \<le> 1 / 2"
  shows
    "real (N + k + 1) * rho ^ k \<le>
      real (N + k + 1) * ((1 / 2 :: real) ^ k)"
proof -
  have power_bound: "rho ^ k \<le> ((1 / 2 :: real) ^ k)"
    by (rule power_mono[OF rho_half rho_nonnegative])
  show ?thesis
    by (rule mult_left_mono[OF power_bound]) simp
qed

lemma slp_weighted_inner_summable:
  fixes rho :: real
  assumes rho_nonnegative: "0 \<le> rho"
    and rho_half: "rho \<le> 1 / 2"
  shows "summable (\<lambda>k. real (N + k + 1) * rho ^ k)"
proof (rule summable_comparison_test'[
    OF slp_weighted_half_series_summable, where N = 0])
  fix k :: nat
  assume "0 \<le> k"
  have term_nonnegative: "0 \<le> real (N + k + 1) * rho ^ k"
    using rho_nonnegative by simp
  have term_bound:
    "real (N + k + 1) * rho ^ k \<le>
      real (N + k + 1) * ((1 / 2 :: real) ^ k)"
    by (rule slp_weighted_inner_term_le_half[
          OF rho_nonnegative rho_half])
  show
    "norm (real (N + k + 1) * rho ^ k) \<le>
      real (N + k + 1) * ((1 / 2 :: real) ^ k)"
    using term_nonnegative term_bound by simp
qed

theorem slp_weighted_geometric_tail_le:
  fixes rho :: real
  assumes rho_nonnegative: "0 \<le> rho"
    and rho_half: "rho \<le> 1 / 2"
  shows
    "slp_weighted_geometric_tail rho N \<le>
      slp_weighted_tail_constant N * rho ^ N"
proof -
  have inner_summable:
    "summable (\<lambda>k. real (N + k + 1) * rho ^ k)"
    by (rule slp_weighted_inner_summable[
          OF rho_nonnegative rho_half])
  have inner_bound:
    "(\<Sum>k. real (N + k + 1) * rho ^ k) \<le>
      slp_weighted_tail_constant N"
    unfolding slp_weighted_tail_constant_def
    by (rule suminf_le[
          OF slp_weighted_inner_term_le_half[
            OF rho_nonnegative rho_half]
          inner_summable slp_weighted_half_series_summable])
  have tail_factorization:
    "slp_weighted_geometric_tail rho N =
      rho ^ N * (\<Sum>k. real (N + k + 1) * rho ^ k)"
  proof -
    have term_identity:
      "(\<lambda>k. real (N + k + 1) * rho ^ (N + k)) =
        (\<lambda>k. rho ^ N * (real (N + k + 1) * rho ^ k))"
      by (rule ext) (simp add: power_add mult.assoc mult.commute mult.left_commute)
    have factor_sum:
      "(\<Sum>k. rho ^ N * (real (N + k + 1) * rho ^ k)) =
        rho ^ N * (\<Sum>k. real (N + k + 1) * rho ^ k)"
      by (rule suminf_mult[OF inner_summable])
    show ?thesis
      unfolding slp_weighted_geometric_tail_def
      using term_identity factor_sum by simp
  qed
  have power_nonnegative: "0 \<le> rho ^ N"
    by (rule zero_le_power[OF rho_nonnegative])
  have scaled_bound:
    "rho ^ N * (\<Sum>k. real (N + k + 1) * rho ^ k) \<le>
      rho ^ N * slp_weighted_tail_constant N"
    by (rule mult_left_mono[OF inner_bound power_nonnegative])
  show ?thesis
    using tail_factorization scaled_bound
    by (simp add: mult.commute)
qed

end
