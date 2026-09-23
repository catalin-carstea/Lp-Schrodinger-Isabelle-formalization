theory Inverse_Schrodinger_Lp_Neumann_Iterates
  imports Inverse_Schrodinger_Lp_Neumann_Recurrence
begin

section \<open>Abstract Neumann operator iterates\<close>

definition slp_neumann_iterate :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a" where
  "slp_neumann_iterate S B j = (S ^^ j) B"

lemma slp_neumann_iterate_zero [simp]:
  "slp_neumann_iterate S B 0 = B"
  by (simp add: slp_neumann_iterate_def)

lemma slp_neumann_iterate_Suc [simp]:
  "slp_neumann_iterate S B (Suc j) = S (slp_neumann_iterate S B j)"
  by (simp add: slp_neumann_iterate_def)

lemma slp_neumann_iterate_norm_le:
  fixes S :: "'a::real_normed_vector \<Rightarrow> 'a"
    and B :: 'a
    and rho :: real
  assumes rho_nonnegative: "0 \<le> rho"
    and contraction: "\<And>f. norm (S f) \<le> rho * norm f"
  shows "norm (slp_neumann_iterate S B j) \<le> norm B * rho ^ j"
proof -
  have recurrence: "\<And>k. norm (slp_neumann_iterate S B (Suc k))
      \<le> rho * norm (slp_neumann_iterate S B k)"
    by (simp add: contraction)
  have "norm (slp_neumann_iterate S B j)
      \<le> norm (slp_neumann_iterate S B 0) * rho ^ j"
    by (rule slp_neumann_recurrence_geometric_bound[
          where a = "\<lambda>j. norm (slp_neumann_iterate S B j)"
            and rho = rho and j = j,
          OF rho_nonnegative recurrence])
  then show ?thesis by simp
qed

lemma slp_neumann_iterate_norms_summable:
  fixes S :: "'a::real_normed_vector \<Rightarrow> 'a"
    and B :: 'a
    and rho :: real
  assumes rho_nonnegative: "0 \<le> rho"
    and rho_strict: "rho < 1"
    and contraction: "\<And>f. norm (S f) \<le> rho * norm f"
  shows "summable (\<lambda>j. norm (slp_neumann_iterate S B j))"
proof -
  have nonnegative: "\<And>j. 0 \<le> norm (slp_neumann_iterate S B j)"
    by simp
  have recurrence: "\<And>j. norm (slp_neumann_iterate S B (Suc j))
      \<le> rho * norm (slp_neumann_iterate S B j)"
    by (simp add: contraction)
  show ?thesis
    by (rule slp_neumann_recurrence_summable[
          where a = "\<lambda>j. norm (slp_neumann_iterate S B j)"
            and rho = rho,
          OF rho_nonnegative rho_strict nonnegative recurrence])
qed

theorem slp_neumann_iterate_norm_suminf_le:
  fixes S :: "'a::real_normed_vector \<Rightarrow> 'a"
    and B :: 'a
    and rho :: real
  assumes rho_nonnegative: "0 \<le> rho"
    and rho_strict: "rho < 1"
    and contraction: "\<And>f. norm (S f) \<le> rho * norm f"
  shows "(\<Sum>j. norm (slp_neumann_iterate S B j)) \<le> norm B / (1 - rho)"
proof -
  have nonnegative: "\<And>j. 0 \<le> norm (slp_neumann_iterate S B j)"
    by simp
  have recurrence: "\<And>j. norm (slp_neumann_iterate S B (Suc j))
      \<le> rho * norm (slp_neumann_iterate S B j)"
    by (simp add: contraction)
  have result:
    "(\<Sum>j. norm (slp_neumann_iterate S B j))
      \<le> norm (slp_neumann_iterate S B 0) / (1 - rho)"
    by (rule slp_neumann_recurrence_suminf_le[
          where a = "\<lambda>j. norm (slp_neumann_iterate S B j)"
            and rho = rho,
          OF rho_nonnegative rho_strict nonnegative recurrence])
  then show ?thesis by simp
qed

corollary slp_neumann_iterates_summable:
  fixes S :: "'a::banach \<Rightarrow> 'a"
    and B :: 'a
    and rho :: real
  assumes rho_nonnegative: "0 \<le> rho"
    and rho_strict: "rho < 1"
    and contraction: "\<And>f. norm (S f) \<le> rho * norm f"
  shows "summable (slp_neumann_iterate S B)"
  by (rule summable_norm_cancel,
      rule slp_neumann_iterate_norms_summable[OF assms])

lemma slp_neumann_iterate_secondary_le:
  fixes S :: "'a::real_normed_vector \<Rightarrow> 'a"
    and B :: 'a
    and secondary :: "'a \<Rightarrow> real"
    and rho D :: real
  assumes rho_nonnegative: "0 \<le> rho"
    and D_nonnegative: "0 \<le> D"
    and primary_step: "\<And>f. norm (S f) \<le> rho * norm f"
    and secondary_step: "\<And>f. secondary (S f) \<le> D * norm f"
  shows "secondary (slp_neumann_iterate S B (Suc j))
      \<le> D * norm B * rho ^ j"
proof -
  have primary_recurrence:
    "\<And>k. norm (slp_neumann_iterate S B (Suc k))
      \<le> rho * norm (slp_neumann_iterate S B k)"
    by (simp add: primary_step)
  have secondary_recurrence:
    "\<And>k. secondary (slp_neumann_iterate S B (Suc k))
      \<le> D * norm (slp_neumann_iterate S B k)"
    by (simp add: secondary_step)
  have result:
    "secondary (slp_neumann_iterate S B (Suc j))
      \<le> D * norm (slp_neumann_iterate S B 0) * rho ^ j"
    by (rule slp_neumann_secondary_norm_bound[
          where a = "\<lambda>j. norm (slp_neumann_iterate S B j)"
            and b = "\<lambda>j. secondary (slp_neumann_iterate S B j)"
            and rho = rho and D = D and j = j,
          OF rho_nonnegative D_nonnegative primary_recurrence
            secondary_recurrence])
  then show ?thesis by simp
qed

end
