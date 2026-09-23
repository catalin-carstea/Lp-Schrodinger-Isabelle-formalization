theory Inverse_Schrodinger_Lp_W1p_Zero_Pair_AE_Subsequence
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_011.Inverse_Schrodinger_Lp_W1p_Zero_Pair_Target_Cauchy"
begin

section \<open>Source-power convergence and a concrete almost-everywhere subsequence\<close>

theorem slp_w1p_function_power_integral_tendsto_zero:
  assumes exponent_positive: "0 < p"
    and error_pairs: "\<And>n. slp_w1p_pair_on p X (e n) (De n)"
    and error_norm_tends:
      "((\<lambda>n. slp_w1p_norm_on p X (e n) (De n)) \<longlongrightarrow> 0) sequentially"
  shows "((\<lambda>n. integral\<^sup>L lborel
      (\<lambda>x. Real_Vector_Spaces.norm
        (slp_restrict_field X (e n) x) powr p)) \<longlongrightarrow> 0) sequentially"
proof -
  let ?I = "\<lambda>n. integral\<^sup>L lborel
    (\<lambda>x. Real_Vector_Spaces.norm
      (slp_restrict_field X (e n) x) powr p)"
  let ?R = "\<lambda>n. ?I n powr (1 / p)"
  let ?W = "\<lambda>n. slp_w1p_norm_on p X (e n) (De n)"
  have integral_nonnegative: "0 \<le> ?I n" for n
    by (rule Bochner_Integration.integral_nonneg) simp
  have root_nonnegative: "0 \<le> ?R n" for n
    by simp
  have root_bound: "?R n \<le> ?W n" for n
    using slp_w1p_norm_on_component_bounds[OF exponent_positive error_pairs]
    unfolding aim_complex_lp_norm_def by blast
  have root_tends: "(?R \<longlongrightarrow> 0) sequentially"
    by (rule tendsto_sandwich[where f = "\<lambda>_. 0" and h = ?W])
      (use root_nonnegative root_bound error_norm_tends in auto)
  have powered_tends: "((\<lambda>n. ?R n powr p) \<longlongrightarrow> 0) sequentially"
  proof -
    have "((\<lambda>n. ?R n powr p) \<longlongrightarrow> 0 powr p) sequentially"
      by (rule tendsto_powr2[OF root_tends tendsto_const])
        (use root_nonnegative exponent_positive in auto)
    then show ?thesis using exponent_positive by simp
  qed
  have root_power: "?R n powr p = ?I n" for n
    using exponent_positive integral_nonnegative[of n]
    by (simp add: powr_powr)
  show ?thesis
    using powered_tends by (simp only: root_power)
qed

theorem slp_w1p_zero_pair_function_AE_subsequence:
  assumes exponent_lower: "1 < a"
    and zero_pair: "slp_w1p_zero_pair_on a X u Du"
  shows "\<exists>phi :: nat \<Rightarrow> slp_scalar_field. \<exists>r :: nat \<Rightarrow> nat.
    (\<forall>n. slp_test_function_on X (phi n) \<and>
      slp_w1p_pair_on a X (phi n) (slp_classical_gradient (phi n))) \<and>
    (\<forall>epsilon>0. \<exists>N. \<forall>n\<ge>N.
      slp_w1p_norm_on a X
        (\<lambda>x. phi n x - u x)
        (\<lambda>x. slp_classical_gradient (phi n) x - Du x) < epsilon) \<and>
    strict_mono r \<and>
    (AE x in lborel.
      (\<lambda>n. phi (r n) x - slp_restrict_field X u x) \<longlonglongrightarrow> 0)"
proof -
  have exponent_positive: "0 < a"
    using exponent_lower by linarith
  have exponent_one_le: "1 \<le> a"
    using exponent_lower by linarith
  obtain phi :: "nat \<Rightarrow> slp_scalar_field" where
      phi_pairs:
        "\<forall>n. slp_test_function_on X (phi n) \<and>
          slp_w1p_pair_on a X (phi n) (slp_classical_gradient (phi n))"
    and phi_converges:
        "\<forall>epsilon>0. \<exists>N. \<forall>n\<ge>N.
          slp_w1p_norm_on a X
            (\<lambda>x. phi n x - u x)
            (\<lambda>x. slp_classical_gradient (phi n) x - Du x) < epsilon"
    using zero_pair unfolding slp_w1p_zero_pair_on_def by blast
  have rough_pair: "slp_w1p_pair_on a X u Du"
    using zero_pair unfolding slp_w1p_zero_pair_on_def by blast
  let ?e = "\<lambda>n x. phi n x - u x"
  let ?De = "\<lambda>n x. slp_classical_gradient (phi n) x - Du x"
  let ?W = "\<lambda>n. slp_w1p_norm_on a X (?e n) (?De n)"
  have error_pairs: "slp_w1p_pair_on a X (?e n) (?De n)" for n
    by (rule slp_w1p_pair_on_diff[OF exponent_one_le
          conjunct2[OF spec[OF phi_pairs]] rough_pair])
  have error_norm_nonnegative: "0 \<le> ?W n" for n
    unfolding slp_w1p_norm_on_def by simp
  have error_norm_tends: "(?W \<longlongrightarrow> 0) sequentially"
  proof (rule metric_LIMSEQ_I)
    fix epsilon :: real
    assume epsilon_positive: "0 < epsilon"
    obtain N where tail: "\<forall>n\<ge>N. ?W n < epsilon"
      using phi_converges epsilon_positive by blast
    show "\<exists>N. \<forall>n\<ge>N. dist (?W n) 0 < epsilon"
      by (rule exI[of _ N])
        (use tail error_norm_nonnegative in auto)
  qed
  have power_integral_tends:
      "((\<lambda>n. integral\<^sup>L lborel
        (\<lambda>x. Real_Vector_Spaces.norm
          (slp_restrict_field X (?e n) x) powr a)) \<longlongrightarrow> 0)
        sequentially"
    by (rule slp_w1p_function_power_integral_tendsto_zero[
          OF exponent_positive error_pairs error_norm_tends])
  have power_integrable:
      "integrable lborel
        (\<lambda>x. Real_Vector_Spaces.norm
          (slp_restrict_field X (?e n) x) powr a)" for n
    by (rule slp_w1p_pair_power_integrable(1)[OF error_pairs])
  have power_L1_tends:
      "((\<lambda>n. integral\<^sup>L lborel
        (\<lambda>x. Real_Vector_Spaces.norm
          (Real_Vector_Spaces.norm
            (slp_restrict_field X (?e n) x) powr a))) \<longlongrightarrow> 0)
        sequentially"
    using power_integral_tends by simp
  obtain r :: "nat \<Rightarrow> nat" where r_strict: "strict_mono r"
    and power_AE:
      "AE x in lborel.
        (\<lambda>n. Real_Vector_Spaces.norm
          (slp_restrict_field X (?e (r n)) x) powr a) \<longlonglongrightarrow> 0"
    using tendsto_L1_AE_subseq[OF power_integrable power_L1_tends] by blast
  have error_AE:
      "AE x in lborel.
        (\<lambda>n. slp_restrict_field X (?e (r n)) x) \<longlonglongrightarrow> 0"
  proof (use power_AE in eventually_elim)
    fix x
    assume power_tends:
      "(\<lambda>n. Real_Vector_Spaces.norm
        (slp_restrict_field X (?e (r n)) x) powr a) \<longlonglongrightarrow> 0"
    have inverse_positive: "0 < 1 / a"
      using exponent_positive by simp
    have norm_tends:
        "(\<lambda>n. Real_Vector_Spaces.norm
          (slp_restrict_field X (?e (r n)) x)) \<longlonglongrightarrow> 0"
    proof -
      have "((\<lambda>n. (Real_Vector_Spaces.norm
          (slp_restrict_field X (?e (r n)) x) powr a) powr (1 / a))
          \<longlongrightarrow> 0 powr (1 / a)) sequentially"
        by (rule tendsto_powr2[OF power_tends tendsto_const])
          (use inverse_positive in auto)
      then show ?thesis
        using exponent_positive by (simp add: powr_powr)
    qed
    show "(\<lambda>n. slp_restrict_field X (?e (r n)) x) \<longlonglongrightarrow> 0"
      using norm_tends tendsto_norm_zero_iff by blast
  qed
  have restricted_error:
      "slp_restrict_field X (?e n) =
        (\<lambda>x. phi n x - slp_restrict_field X u x)" for n
  proof -
    have phi_restricted: "slp_restrict_field X (phi n) = phi n"
      by (rule slp_test_function_restrict_field_eq[
            OF conjunct1[OF spec[OF phi_pairs]]])
    have "slp_restrict_field X (?e n) =
        (\<lambda>x. slp_restrict_field X (phi n) x -
          slp_restrict_field X u x)"
      by (rule ext) (simp add: slp_restrict_field_def)
    also have "\<dots> = (\<lambda>x. phi n x - slp_restrict_field X u x)"
      using phi_restricted by simp
    finally show ?thesis .
  qed
  have representative_AE:
      "AE x in lborel.
        (\<lambda>n. phi (r n) x - slp_restrict_field X u x) \<longlonglongrightarrow> 0"
    using error_AE by (simp only: restricted_error)
  show ?thesis
    by (rule exI[of _ phi], rule exI[of _ r])
      (use phi_pairs phi_converges r_strict representative_AE in blast)
qed

end
