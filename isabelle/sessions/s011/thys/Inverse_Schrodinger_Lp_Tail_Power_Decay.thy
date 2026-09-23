theory Inverse_Schrodinger_Lp_Tail_Power_Decay
  imports Inverse_Schrodinger_Lp_Tail_Cutoffs
begin

section \<open>Power decay from the strict tail exponents\<close>

lemma slp_negative_powr_at_top:
  fixes exponent :: real
  assumes exponent_negative: "exponent < 0"
  shows
    "((\<lambda>tau :: real. tau powr exponent) \<longlongrightarrow> 0) at_top"
proof -
  have identity_at_top:
    "filterlim (\<lambda>tau :: real. tau) at_top at_top"
    by (rule filterlim_ident)
  show ?thesis
    by (rule tendsto_neg_powr[OF exponent_negative identity_at_top])
qed

lemma slp_real_constant_negative_powr_at_top:
  fixes exponent C :: real
  assumes exponent_negative: "exponent < 0"
  shows
    "((\<lambda>tau :: real. C * (tau powr exponent))
      \<longlongrightarrow> 0) at_top"
  using tendsto_mult_left[
    OF slp_negative_powr_at_top[OF exponent_negative], of C]
  by simp

lemma slp_complex_constant_negative_powr_at_top:
  fixes exponent :: real and C :: complex
  assumes exponent_negative: "exponent < 0"
  shows
    "((\<lambda>tau :: real. of_real (tau powr exponent) * C)
      \<longlongrightarrow> 0) at_top"
proof -
  have real_decay:
    "((\<lambda>tau :: real. tau powr exponent) \<longlongrightarrow> 0) at_top"
    by (rule slp_negative_powr_at_top[OF exponent_negative])
  have complex_decay_raw:
    "((\<lambda>tau :: real. of_real (tau powr exponent) :: complex)
      \<longlongrightarrow> of_real (0 :: real)) at_top"
    using real_decay by (simp only: tendsto_of_real_iff)
  have complex_decay:
    "((\<lambda>tau :: real. of_real (tau powr exponent) :: complex)
      \<longlongrightarrow> 0) at_top"
    using complex_decay_raw by simp
  show ?thesis
    using tendsto_mult_right[OF complex_decay, of C] by simp
qed

theorem slp_tail_cutoff1_powr_decay:
  assumes alpha_positive: "0 < alpha"
  shows
    "((\<lambda>tau :: real.
        tau powr
          (1 - s - alpha * of_int (slp_tail_cutoff1 alpha s)))
      \<longlongrightarrow> 0) at_top"
  by (rule slp_negative_powr_at_top)
    (rule slp_tail_cutoff1_strict[OF alpha_positive])

theorem slp_tail_cutoff2_powr_decay:
  assumes alpha_positive: "0 < alpha"
  shows
    "((\<lambda>tau :: real.
        tau powr
          (1 - s - alpha -
            alpha * of_int (slp_tail_cutoff2 alpha s)))
      \<longlongrightarrow> 0) at_top"
  by (rule slp_negative_powr_at_top)
    (rule slp_tail_cutoff2_strict[OF alpha_positive])

corollary slp_tail_cutoff1_complex_scaled_decay:
  fixes C :: complex
  assumes alpha_positive: "0 < alpha"
  shows
    "((\<lambda>tau :: real.
        of_real
          (tau powr
            (1 - s - alpha * of_int (slp_tail_cutoff1 alpha s))) * C)
      \<longlongrightarrow> 0) at_top"
  by (rule slp_complex_constant_negative_powr_at_top[
        where exponent =
          "1 - s - alpha * of_int (slp_tail_cutoff1 alpha s)" and C = C])
    (rule slp_tail_cutoff1_strict[OF alpha_positive])

corollary slp_tail_cutoff2_complex_scaled_decay:
  fixes C :: complex
  assumes alpha_positive: "0 < alpha"
  shows
    "((\<lambda>tau :: real.
        of_real
          (tau powr
            (1 - s - alpha -
              alpha * of_int (slp_tail_cutoff2 alpha s))) * C)
      \<longlongrightarrow> 0) at_top"
  by (rule slp_complex_constant_negative_powr_at_top[
        where exponent =
          "1 - s - alpha -
            alpha * of_int (slp_tail_cutoff2 alpha s)" and C = C])
    (rule slp_tail_cutoff2_strict[OF alpha_positive])

end
