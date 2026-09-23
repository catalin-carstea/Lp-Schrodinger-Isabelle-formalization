theory Inverse_Schrodinger_Lp_Cauchy_Power_Error
  imports Inverse_Schrodinger_Lp_Scaled_Young_Limit
begin

section \<open>Fixed-output Cauchy decay from a vanishing power error\<close>

theorem slp_cauchy_weighted_L1_tendsto_of_power_error:
  fixes b R :: real
    and h :: "nat \<Rightarrow> slp_point \<Rightarrow> complex"
  assumes exponent: "2 < b"
    and radius_nonnegative: "0 \<le> R"
    and h_lp: "\<And>n. aim_complex_lp_on_plane b (h n)"
    and support_radius:
      "\<And>n y. h n y \<noteq> 0 \<Longrightarrow> norm (z - y) \<le> R"
    and error_limit:
      "((\<lambda>n. \<integral>y. norm (h n y) powr b \<partial>lborel)
        \<longlongrightarrow> 0) sequentially"
  shows "((\<lambda>n. \<integral>\<^sup>+y.
      norm (slp_cauchy_integrand orientation (h n) z y) \<partial>lborel)
    \<longlongrightarrow> 0) sequentially"
proof -
  let ?e = "\<lambda>n. \<integral>y. norm (h n y) powr b \<partial>lborel"
  let ?a = "slp_regularized_error_scale b ?e"
  let ?q = "slp_holder_conjugate b"
  have error_nonnegative: "0 \<le> ?e n" for n
    by (rule Bochner_Integration.integral_nonneg) simp
  have scale_positive: "0 < ?a n" for n
    by (rule slp_regularized_error_scale_positive[OF
          exponent error_nonnegative])
  have majorant_limit:
      "((\<lambda>n. \<integral>y.
        (?a n * slp_localized_cauchy_kernel R (z - y)) powr ?q / ?q +
        (inverse (?a n) * norm (h n y)) powr b / b \<partial>lborel)
        \<longlongrightarrow> 0) sequentially"
    by (rule slp_scaled_young_majorant_tendsto_zero_of_power_error[OF
          exponent h_lp error_limit])
  show ?thesis
    by (rule slp_cauchy_weighted_L1_tendsto_of_scaled_young[OF
          exponent radius_nonnegative scale_positive h_lp support_radius
          majorant_limit])
qed

end
