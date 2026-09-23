theory Inverse_Schrodinger_Lp_Neumann_Fixed_Point
  imports Inverse_Schrodinger_Lp_Neumann_Iterates
begin

section \<open>Summed Neumann fixed point\<close>

definition slp_neumann_sum :: "('a::banach \<Rightarrow>\<^sub>L 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "slp_neumann_sum S B = (\<Sum>j. slp_neumann_iterate (\<lambda>f. S f) B j)"

lemma slp_neumann_sum_norm_le:
  fixes S :: "'a::banach \<Rightarrow>\<^sub>L 'a"
    and B :: 'a
    and rho :: real
  assumes rho_nonnegative: "0 \<le> rho"
    and rho_strict: "rho < 1"
    and contraction: "\<And>f. norm (S f) \<le> rho * norm f"
  shows "norm (slp_neumann_sum S B) \<le> norm B / (1 - rho)"
proof -
  have norm_summable:
    "summable (\<lambda>j. norm (slp_neumann_iterate (\<lambda>f. S f) B j))"
    by (rule slp_neumann_iterate_norms_summable[
          OF rho_nonnegative rho_strict contraction])
  have first:
    "norm (slp_neumann_sum S B)
      \<le> (\<Sum>j. norm (slp_neumann_iterate (\<lambda>f. S f) B j))"
    unfolding slp_neumann_sum_def
    by (rule summable_norm[OF norm_summable])
  have second:
    "(\<Sum>j. norm (slp_neumann_iterate (\<lambda>f. S f) B j))
      \<le> norm B / (1 - rho)"
    by (rule slp_neumann_iterate_norm_suminf_le[
          OF rho_nonnegative rho_strict contraction])
  show ?thesis
    using first second by (rule order_trans)
qed

theorem slp_neumann_sum_fixed_point:
  fixes S :: "'a::banach \<Rightarrow>\<^sub>L 'a"
    and B :: 'a
    and rho :: real
  assumes rho_nonnegative: "0 \<le> rho"
    and rho_strict: "rho < 1"
    and contraction: "\<And>f. norm (S f) \<le> rho * norm f"
  shows "slp_neumann_sum S B = B + S (slp_neumann_sum S B)"
proof -
  let ?U = "slp_neumann_iterate (\<lambda>f. S f) B"
  have U_summable: "summable ?U"
    by (rule slp_neumann_iterates_summable[
          OF rho_nonnegative rho_strict contraction])
  have image_sum:
    "S (\<Sum>j. ?U j) = (\<Sum>j. S (?U j))"
    by (rule bounded_linear.suminf[
          OF blinfun.bounded_linear_right U_summable])
  have recurrence: "(\<lambda>j. S (?U j)) = (\<lambda>j. ?U (Suc j))"
    by (rule ext, simp)
  have shifted: "(\<Sum>j. ?U (Suc j)) = (\<Sum>j. ?U j) - B"
    using suminf_split_head[OF U_summable]
    by simp
  have image_suminf_eq:
    "(\<Sum>j. S (?U j)) = (\<Sum>j. ?U (Suc j))"
    by (rule arg_cong[where f = suminf, OF recurrence])
  have image_shifted:
    "S (\<Sum>j. ?U j) = (\<Sum>j. ?U (Suc j))"
    using image_sum image_suminf_eq by (rule trans)
  have S_sum: "S (\<Sum>j. ?U j) = (\<Sum>j. ?U j) - B"
    using image_shifted shifted by (rule trans)
  have "(\<Sum>j. ?U j) = B + S (\<Sum>j. ?U j)"
    using S_sum by simp
  then show ?thesis
    by (simp add: slp_neumann_sum_def)
qed

lemma slp_contraction_affine_fixed_point_unique:
  fixes S :: "'a::real_normed_vector \<Rightarrow>\<^sub>L 'a"
    and B X Y :: 'a
    and rho :: real
  assumes rho_strict: "rho < 1"
    and contraction: "\<And>f. norm (S f) \<le> rho * norm f"
    and X_fixed: "X = B + S X"
    and Y_fixed: "Y = B + S Y"
  shows "X = Y"
proof -
  have difference: "X - Y = S (X - Y)"
  proof -
    have "X - Y = (B + S X) - (B + S Y)"
      using X_fixed Y_fixed by simp
    also have "... = S X - S Y"
      by simp
    also have "... = S (X - Y)"
      by (rule blinfun.diff_right[symmetric])
    finally show ?thesis .
  qed
  have norm_le: "norm (X - Y) \<le> rho * norm (X - Y)"
    using contraction[of "X - Y"] difference by simp
  have not_positive: "\<not> 0 < norm (X - Y)"
  proof
    assume positive: "0 < norm (X - Y)"
    have "rho * norm (X - Y) < 1 * norm (X - Y)"
      by (rule mult_strict_right_mono[OF rho_strict positive])
    with norm_le show False by simp
  qed
  have "norm (X - Y) = 0"
    using norm_ge_zero[of "X - Y"] not_positive by linarith
  then show ?thesis by simp
qed

corollary slp_neumann_sum_unique_fixed_point:
  fixes S :: "'a::banach \<Rightarrow>\<^sub>L 'a"
    and B X :: 'a
    and rho :: real
  assumes rho_nonnegative: "0 \<le> rho"
    and rho_strict: "rho < 1"
    and contraction: "\<And>f. norm (S f) \<le> rho * norm f"
    and X_fixed: "X = B + S X"
  shows "X = slp_neumann_sum S B"
  by (rule slp_contraction_affine_fixed_point_unique[
        OF rho_strict contraction X_fixed
          slp_neumann_sum_fixed_point[OF rho_nonnegative rho_strict contraction]])

end
