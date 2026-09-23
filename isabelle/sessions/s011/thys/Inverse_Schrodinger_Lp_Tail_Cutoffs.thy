theory Inverse_Schrodinger_Lp_Tail_Cutoffs
  imports Inverse_Schrodinger_Lp_Leading_Functional
begin

section \<open>Strict Neumann-tail cutoffs\<close>

definition slp_tail_cutoff1 :: "real \<Rightarrow> real \<Rightarrow> int"
where
  "slp_tail_cutoff1 alpha s =
    floor ((1 - s) / alpha) + 1"

definition slp_tail_cutoff2 :: "real \<Rightarrow> real \<Rightarrow> int"
where
  "slp_tail_cutoff2 alpha s =
    max 0 (floor ((1 - s - alpha) / alpha) + 1)"

lemma slp_tail_cutoff1_nonnegative:
  assumes alpha_positive: "0 < alpha"
    and s_at_most_one: "s \<le> 1"
  shows "0 \<le> slp_tail_cutoff1 alpha s"
proof -
  have numerator_nonnegative: "0 \<le> 1 - s"
    using s_at_most_one by linarith
  have ratio_nonnegative: "0 \<le> (1 - s) / alpha"
    by (rule divide_nonneg_pos[OF numerator_nonnegative alpha_positive])
  then have "0 \<le> floor ((1 - s) / alpha)"
    by simp
  then show ?thesis
    unfolding slp_tail_cutoff1_def by linarith
qed

lemma slp_tail_cutoff1_strict:
  assumes alpha_positive: "0 < alpha"
  shows
    "1 - s -
      alpha * of_int (slp_tail_cutoff1 alpha s) < 0"
proof -
  let ?x = "(1 - s) / alpha"
  have floor_upper: "?x < of_int (floor ?x + 1)"
    using floor_correct[of ?x] by simp
  have scaled:
    "alpha * ?x < alpha * of_int (floor ?x + 1)"
    by (rule mult_strict_left_mono[OF floor_upper alpha_positive])
  have cancel: "alpha * ?x = 1 - s"
    using alpha_positive by simp
  show ?thesis
    unfolding slp_tail_cutoff1_def
    using scaled cancel by linarith
qed

lemma slp_tail_cutoff1_least:
  assumes alpha_positive: "0 < alpha"
    and exponent_negative:
      "1 - s - alpha * of_int n < 0"
  shows "slp_tail_cutoff1 alpha s \<le> n"
proof -
  have ratio_less: "(1 - s) / alpha < of_int n"
    using alpha_positive exponent_negative
    by (subst pos_divide_less_eq[OF alpha_positive])
      (simp add: mult.commute; linarith)
  have "floor ((1 - s) / alpha) < n"
    using ratio_less by (simp only: floor_less_iff)
  then show ?thesis
    unfolding slp_tail_cutoff1_def by linarith
qed

theorem slp_tail_cutoff1_is_least_nonnegative:
  assumes alpha_positive: "0 < alpha"
    and s_at_most_one: "s \<le> 1"
  shows
    "0 \<le> slp_tail_cutoff1 alpha s \<and>
      1 - s -
        alpha * of_int (slp_tail_cutoff1 alpha s) < 0 \<and>
      (\<forall>n. 0 \<le> n \<longrightarrow>
        1 - s - alpha * of_int n < 0 \<longrightarrow>
        slp_tail_cutoff1 alpha s \<le> n)"
  using slp_tail_cutoff1_nonnegative[OF alpha_positive s_at_most_one]
    slp_tail_cutoff1_strict[OF alpha_positive]
    slp_tail_cutoff1_least[OF alpha_positive]
  by blast

lemma slp_tail_cutoff2_nonnegative:
  "0 \<le> slp_tail_cutoff2 alpha s"
  unfolding slp_tail_cutoff2_def by simp

lemma slp_tail_cutoff2_strict:
  assumes alpha_positive: "0 < alpha"
  shows
    "1 - s - alpha -
      alpha * of_int (slp_tail_cutoff2 alpha s) < 0"
proof (cases "floor ((1 - s - alpha) / alpha) + 1 \<le> 0")
  case True
  then have floor_negative:
    "floor ((1 - s - alpha) / alpha) < 0"
    by linarith
  then have ratio_negative:
    "(1 - s - alpha) / alpha < 0"
    by simp
  then have numerator_negative: "1 - s - alpha < 0"
    using pos_divide_less_eq[OF alpha_positive,
      of "1 - s - alpha" 0]
    by simp
  show ?thesis
    using True numerator_negative
    unfolding slp_tail_cutoff2_def by simp
next
  case False
  let ?y = "(1 - s - alpha) / alpha"
  have cutoff_identity:
    "slp_tail_cutoff2 alpha s = floor ?y + 1"
    using False unfolding slp_tail_cutoff2_def by simp
  have floor_upper: "?y < of_int (floor ?y + 1)"
    using floor_correct[of ?y] by simp
  have scaled:
    "alpha * ?y < alpha * of_int (floor ?y + 1)"
    by (rule mult_strict_left_mono[OF floor_upper alpha_positive])
  have cancel: "alpha * ?y = 1 - s - alpha"
    using alpha_positive by simp
  show ?thesis
    unfolding cutoff_identity
    using scaled cancel by linarith
qed

lemma slp_tail_cutoff2_least:
  assumes alpha_positive: "0 < alpha"
    and n_nonnegative: "0 \<le> n"
    and exponent_negative:
      "1 - s - alpha - alpha * of_int n < 0"
  shows "slp_tail_cutoff2 alpha s \<le> n"
proof -
  have ratio_less:
    "(1 - s - alpha) / alpha < of_int n"
    using alpha_positive exponent_negative
    by (subst pos_divide_less_eq[OF alpha_positive])
      (simp add: mult.commute; linarith)
  have floor_less:
    "floor ((1 - s - alpha) / alpha) < n"
    using ratio_less by (simp only: floor_less_iff)
  have successor_at_most:
    "floor ((1 - s - alpha) / alpha) + 1 \<le> n"
    using floor_less by linarith
  show ?thesis
    unfolding slp_tail_cutoff2_def
    using n_nonnegative successor_at_most by simp
qed

theorem slp_tail_cutoff2_is_least_nonnegative:
  assumes alpha_positive: "0 < alpha"
  shows
    "0 \<le> slp_tail_cutoff2 alpha s \<and>
      1 - s - alpha -
        alpha * of_int (slp_tail_cutoff2 alpha s) < 0 \<and>
      (\<forall>n. 0 \<le> n \<longrightarrow>
        1 - s - alpha - alpha * of_int n < 0 \<longrightarrow>
        slp_tail_cutoff2 alpha s \<le> n)"
  using slp_tail_cutoff2_nonnegative[of alpha s]
    slp_tail_cutoff2_strict[OF alpha_positive]
    slp_tail_cutoff2_least[OF alpha_positive]
  by blast

end
