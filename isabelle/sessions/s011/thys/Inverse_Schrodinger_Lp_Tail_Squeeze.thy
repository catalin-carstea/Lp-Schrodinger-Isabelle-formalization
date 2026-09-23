theory Inverse_Schrodinger_Lp_Tail_Squeeze
  imports Inverse_Schrodinger_Lp_Mixed_Diagonal_Tail
begin

section \<open>Squeezing nonnegative tails by negative powers\<close>

lemma slp_nonnegative_negative_powr_bound_tendsto_zero:
  fixes tail :: "real \<Rightarrow> real"
    and exponent C :: real
  assumes exponent_negative: "exponent < 0"
    and C_nonnegative: "0 \<le> C"
    and tail_nonnegative:
      "eventually (\<lambda>tau. 0 \<le> tail tau) at_top"
    and tail_bound:
      "eventually
        (\<lambda>tau. tail tau \<le> C * (tau powr exponent)) at_top"
  shows "(tail \<longlongrightarrow> 0) at_top"
proof -
  have upper_limit:
    "((\<lambda>tau :: real. C * (tau powr exponent))
      \<longlongrightarrow> 0) at_top"
    by (rule slp_real_constant_negative_powr_at_top[
          OF exponent_negative])
  have lower_limit:
    "((\<lambda>_ :: real. 0 :: real) \<longlongrightarrow> 0) at_top"
    by (rule tendsto_const)
  show ?thesis
    by (rule tendsto_sandwich[
          OF tail_nonnegative tail_bound lower_limit upper_limit])
qed

theorem slp_tail_cutoff1_bound_tendsto_zero:
  fixes tail :: "real \<Rightarrow> real"
    and C alpha s :: real
  assumes alpha_positive: "0 < alpha"
    and C_nonnegative: "0 \<le> C"
    and tail_nonnegative:
      "eventually (\<lambda>tau. 0 \<le> tail tau) at_top"
    and tail_bound:
      "eventually
        (\<lambda>tau.
          tail tau \<le>
            C * (tau powr
              (1 - s - alpha * of_int (slp_tail_cutoff1 alpha s))))
        at_top"
  shows "(tail \<longlongrightarrow> 0) at_top"
  by (rule slp_nonnegative_negative_powr_bound_tendsto_zero[
        OF slp_tail_cutoff1_strict[OF alpha_positive]
          C_nonnegative tail_nonnegative tail_bound])

theorem slp_tail_cutoff2_bound_tendsto_zero:
  fixes tail :: "real \<Rightarrow> real"
    and C alpha s :: real
  assumes alpha_positive: "0 < alpha"
    and C_nonnegative: "0 \<le> C"
    and tail_nonnegative:
      "eventually (\<lambda>tau. 0 \<le> tail tau) at_top"
    and tail_bound:
      "eventually
        (\<lambda>tau.
          tail tau \<le>
            C * (tau powr
              (1 - s - alpha -
                alpha * of_int (slp_tail_cutoff2 alpha s))))
        at_top"
  shows "(tail \<longlongrightarrow> 0) at_top"
  by (rule slp_nonnegative_negative_powr_bound_tendsto_zero[
        OF slp_tail_cutoff2_strict[OF alpha_positive]
          C_nonnegative tail_nonnegative tail_bound])

end
