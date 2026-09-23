theory Inverse_Schrodinger_Lp_Neumann_Recurrence
  imports Inverse_Schrodinger_Lp_Neumann_Tails
begin

section \<open>Scalar Neumann-iterate recurrence\<close>

lemma slp_neumann_recurrence_geometric_bound:
  fixes a :: "nat \<Rightarrow> real"
    and rho :: real
  assumes rho_nonnegative: "0 \<le> rho"
    and recurrence: "\<And>j. a (Suc j) \<le> rho * a j"
  shows "a j \<le> a 0 * rho ^ j"
proof (induction j)
  case 0
  show ?case by simp
next
  case (Suc j)
  have scaled:
    "rho * a j \<le> rho * (a 0 * rho ^ j)"
    by (rule mult_left_mono[OF Suc.IH rho_nonnegative])
  have "a (Suc j) \<le> rho * (a 0 * rho ^ j)"
    using recurrence[of j] scaled by (rule order_trans)
  then show ?case
    by (simp add: algebra_simps)
qed

lemma slp_neumann_recurrence_summable:
  fixes a :: "nat \<Rightarrow> real"
    and rho :: real
  assumes rho_nonnegative: "0 \<le> rho"
    and rho_strict: "rho < 1"
    and a_nonnegative: "\<And>j. 0 \<le> a j"
    and recurrence: "\<And>j. a (Suc j) \<le> rho * a j"
  shows "summable a"
proof -
  have rho_norm: "norm rho < 1"
    using rho_nonnegative rho_strict
    by (simp add: real_norm_def abs_of_nonneg)
  have geometric: "summable (\<lambda>j. rho ^ j)"
    by (rule summable_geometric[OF rho_norm])
  have majorant: "summable (\<lambda>j. a 0 * rho ^ j)"
    by (rule summable_mult[OF geometric])
  show ?thesis
  proof (rule summable_comparison_test'[OF majorant, where N = 0])
    fix j :: nat
    assume "0 \<le> j"
    have upper: "a j \<le> a 0 * rho ^ j"
      by (rule slp_neumann_recurrence_geometric_bound[
            where a = a and rho = rho and j = j,
            OF rho_nonnegative recurrence])
    show "norm (a j) \<le> a 0 * rho ^ j"
      using a_nonnegative[of j] upper by simp
  qed
qed

theorem slp_neumann_recurrence_suminf_le:
  fixes a :: "nat \<Rightarrow> real"
    and rho :: real
  assumes rho_nonnegative: "0 \<le> rho"
    and rho_strict: "rho < 1"
    and a_nonnegative: "\<And>j. 0 \<le> a j"
    and recurrence: "\<And>j. a (Suc j) \<le> rho * a j"
  shows "suminf a \<le> a 0 / (1 - rho)"
proof -
  have rho_norm: "norm rho < 1"
    using rho_nonnegative rho_strict
    by (simp add: real_norm_def abs_of_nonneg)
  have geometric: "summable (\<lambda>j. rho ^ j)"
    by (rule summable_geometric[OF rho_norm])
  have majorant_summable: "summable (\<lambda>j. a 0 * rho ^ j)"
    by (rule summable_mult[OF geometric])
  have a_summable: "summable a"
    by (rule slp_neumann_recurrence_summable[
          where a = a and rho = rho,
          OF rho_nonnegative rho_strict a_nonnegative recurrence])
  have upper_sum:
    "suminf (\<lambda>j. a 0 * rho ^ j) = a 0 / (1 - rho)"
    using suminf_mult[OF geometric, of "a 0"]
      suminf_geometric[OF rho_norm]
    by (simp add: divide_inverse)
  have comparison:
    "suminf a \<le> suminf (\<lambda>j. a 0 * rho ^ j)"
  proof (rule suminf_le[OF _ a_summable majorant_summable])
    fix j
    show "a j \<le> a 0 * rho ^ j"
      by (rule slp_neumann_recurrence_geometric_bound[
            where a = a and rho = rho and j = j,
            OF rho_nonnegative recurrence])
  qed
  show ?thesis
    using comparison upper_sum by simp
qed

lemma slp_neumann_secondary_norm_bound:
  fixes a b :: "nat \<Rightarrow> real"
    and rho D :: real
  assumes rho_nonnegative: "0 \<le> rho"
    and D_nonnegative: "0 \<le> D"
    and recurrence: "\<And>j. a (Suc j) \<le> rho * a j"
    and secondary_step: "\<And>j. b (Suc j) \<le> D * a j"
  shows "b (Suc j) \<le> D * a 0 * rho ^ j"
proof -
  have primary: "a j \<le> a 0 * rho ^ j"
    by (rule slp_neumann_recurrence_geometric_bound[
          where a = a and rho = rho and j = j,
          OF rho_nonnegative recurrence])
  have scaled: "D * a j \<le> D * (a 0 * rho ^ j)"
    by (rule mult_left_mono[OF primary D_nonnegative])
  have "b (Suc j) \<le> D * (a 0 * rho ^ j)"
    using secondary_step[of j] scaled by (rule order_trans)
  then show ?thesis
    by (simp add: mult.assoc)
qed

end
