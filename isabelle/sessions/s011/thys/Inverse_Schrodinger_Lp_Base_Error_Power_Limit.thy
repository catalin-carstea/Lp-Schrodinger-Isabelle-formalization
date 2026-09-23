theory Inverse_Schrodinger_Lp_Base_Error_Power_Limit
  imports Inverse_Schrodinger_Lp_Base_Error_Power_Bound
begin

section \<open>Vanishing power integral for the base approximation error\<close>

theorem slp_oscillatory_base_approximation_error_power_tendsto_zero:
  assumes exponent_positive: "0 < b"
    and radius_nonnegative: "0 \<le> R"
    and raw_lp:
      "\<And>n. aim_complex_lp_on_plane b
        (slp_raw_value_approximation_error phi g n)"
    and raw_support:
      "\<And>n x. slp_raw_value_approximation_error phi g n x \<noteq> 0
        \<Longrightarrow> norm (z - x) \<le> R"
    and raw_limit:
      "((\<lambda>n. \<integral>x.
        norm (slp_raw_value_approximation_error phi g n x) powr b
          \<partial>lborel) \<longlongrightarrow> 0) sequentially"
  shows "((\<lambda>n. \<integral>x. norm
      (slp_oscillatory_base_approximation_error tau c phi g n x) powr b
        \<partial>lborel) \<longlongrightarrow> 0) sequentially"
proof -
  let ?M = "R + norm (z - c)"
  have target_nonnegative:
      "0 \<le> (\<integral>x. norm
        (slp_oscillatory_base_approximation_error tau c phi g n x) powr b
          \<partial>lborel)" for n
    by (rule Bochner_Integration.integral_nonneg) simp
  have upper_bound:
      "(\<integral>x. norm
        (slp_oscillatory_base_approximation_error tau c phi g n x) powr b
          \<partial>lborel) \<le>
      ?M powr b *
        (\<integral>x.
          norm (slp_raw_value_approximation_error phi g n x) powr b
            \<partial>lborel)" for n
    by (rule slp_oscillatory_base_approximation_error_power_integral_bound[OF
          exponent_positive radius_nonnegative raw_lp raw_support])
  have majorant_limit:
      "((\<lambda>n. ?M powr b *
        (\<integral>x.
          norm (slp_raw_value_approximation_error phi g n x) powr b
            \<partial>lborel)) \<longlongrightarrow> 0) sequentially"
  proof -
    have "((\<lambda>n. ?M powr b *
        (\<integral>x.
          norm (slp_raw_value_approximation_error phi g n x) powr b
            \<partial>lborel))
      \<longlongrightarrow> ?M powr b * 0) sequentially"
      by (rule tendsto_mult[OF tendsto_const raw_limit])
    then show ?thesis by simp
  qed
  show ?thesis
    by (rule tendsto_sandwich[where f = "\<lambda>_. 0" and
          h = "\<lambda>n. ?M powr b *
            (\<integral>x.
              norm (slp_raw_value_approximation_error phi g n x) powr b
                \<partial>lborel)"])
       (use target_nonnegative upper_bound majorant_limit in auto)
qed

end
