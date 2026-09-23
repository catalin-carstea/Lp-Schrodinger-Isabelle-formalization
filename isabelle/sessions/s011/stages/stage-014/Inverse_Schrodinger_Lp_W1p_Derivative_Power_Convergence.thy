theory Inverse_Schrodinger_Lp_W1p_Derivative_Power_Convergence
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_011.Inverse_Schrodinger_Lp_W1p_Zero_Pair_AE_Subsequence"
begin

section \<open>Derivative-coordinate power convergence from the Sobolev norm\<close>

theorem slp_w1p_derivative_power_integrals_tendsto_zero:
  assumes exponent_positive: "0 < p"
    and error_pairs: "\<And>n. slp_w1p_pair_on p X (e n) (De n)"
    and error_norm_tends:
      "((\<lambda>n. slp_w1p_norm_on p X (e n) (De n)) \<longlongrightarrow> 0)
        sequentially"
  shows derivative_zero:
      "((\<lambda>n. integral\<^sup>L lborel
        (\<lambda>x. Real_Vector_Spaces.norm
          (slp_restrict_field X (\<lambda>y. De n y $ 0) x) powr p))
        \<longlongrightarrow> 0) sequentially"
    and derivative_one:
      "((\<lambda>n. integral\<^sup>L lborel
        (\<lambda>x. Real_Vector_Spaces.norm
          (slp_restrict_field X (\<lambda>y. De n y $ 1) x) powr p))
        \<longlongrightarrow> 0) sequentially"
proof -
  let ?I0 = "\<lambda>n. integral\<^sup>L lborel
    (\<lambda>x. Real_Vector_Spaces.norm
      (slp_restrict_field X (\<lambda>y. De n y $ 0) x) powr p)"
  let ?I1 = "\<lambda>n. integral\<^sup>L lborel
    (\<lambda>x. Real_Vector_Spaces.norm
      (slp_restrict_field X (\<lambda>y. De n y $ 1) x) powr p)"
  let ?R0 = "\<lambda>n. ?I0 n powr (1 / p)"
  let ?R1 = "\<lambda>n. ?I1 n powr (1 / p)"
  let ?W = "\<lambda>n. slp_w1p_norm_on p X (e n) (De n)"
  have I0_nonnegative: "0 \<le> ?I0 n" for n
    by (rule Bochner_Integration.integral_nonneg) simp
  have I1_nonnegative: "0 \<le> ?I1 n" for n
    by (rule Bochner_Integration.integral_nonneg) simp
  have R0_nonnegative: "0 \<le> ?R0 n" for n by simp
  have R1_nonnegative: "0 \<le> ?R1 n" for n by simp
  have R0_bound: "?R0 n \<le> ?W n" for n
    using slp_w1p_norm_on_component_bounds(2)[OF
      exponent_positive error_pairs[of n]]
    unfolding aim_complex_lp_norm_def by blast
  have R1_bound: "?R1 n \<le> ?W n" for n
    using slp_w1p_norm_on_component_bounds(3)[OF
      exponent_positive error_pairs[of n]]
    unfolding aim_complex_lp_norm_def by blast
  have R0_tends: "(?R0 \<longlongrightarrow> 0) sequentially"
    by (rule tendsto_sandwich[where f = "\<lambda>_. 0" and h = ?W])
      (use R0_nonnegative R0_bound error_norm_tends in auto)
  have R1_tends: "(?R1 \<longlongrightarrow> 0) sequentially"
    by (rule tendsto_sandwich[where f = "\<lambda>_. 0" and h = ?W])
      (use R1_nonnegative R1_bound error_norm_tends in auto)
  have R0_power_tends:
      "((\<lambda>n. ?R0 n powr p) \<longlongrightarrow> 0) sequentially"
  proof -
    have "((\<lambda>n. ?R0 n powr p) \<longlongrightarrow> 0 powr p)
        sequentially"
      by (rule tendsto_powr2[OF R0_tends tendsto_const])
        (use R0_nonnegative exponent_positive in auto)
    then show ?thesis using exponent_positive by simp
  qed
  have R1_power_tends:
      "((\<lambda>n. ?R1 n powr p) \<longlongrightarrow> 0) sequentially"
  proof -
    have "((\<lambda>n. ?R1 n powr p) \<longlongrightarrow> 0 powr p)
        sequentially"
      by (rule tendsto_powr2[OF R1_tends tendsto_const])
        (use R1_nonnegative exponent_positive in auto)
    then show ?thesis using exponent_positive by simp
  qed
  have R0_power: "?R0 n powr p = ?I0 n" for n
    using exponent_positive I0_nonnegative[of n]
    by (simp add: powr_powr)
  have R1_power: "?R1 n powr p = ?I1 n" for n
    using exponent_positive I1_nonnegative[of n]
    by (simp add: powr_powr)
  show "(?I0 \<longlongrightarrow> 0) sequentially"
    using R0_power_tends by (simp only: R0_power)
  show "(?I1 \<longlongrightarrow> 0) sequentially"
    using R1_power_tends by (simp only: R1_power)
qed

end
