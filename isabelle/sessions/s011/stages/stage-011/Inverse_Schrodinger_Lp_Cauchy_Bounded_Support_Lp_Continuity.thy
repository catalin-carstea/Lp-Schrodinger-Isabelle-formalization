theory Inverse_Schrodinger_Lp_Cauchy_Bounded_Support_Lp_Continuity
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_011.Inverse_Schrodinger_Lp_Complex_Lp_AE_Cauchy_Closure"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Cauchy_Power_Error"
begin

section \<open>Bounded-support planar-Lp continuity of the ordinary Cauchy transform\<close>

theorem slp_cauchy_transform_tendsto_of_bounded_support_lp_norm:
  fixes b R :: real
    and z :: slp_point
    and f :: "nat \<Rightarrow> slp_scalar_field"
    and g :: slp_scalar_field
  assumes exponent: "2 < b"
    and radius_nonnegative: "0 \<le> R"
    and source_lp: "\<And>n. aim_complex_lp_on_plane b (f n)"
    and target_lp: "aim_complex_lp_on_plane b g"
    and source_support:
      "\<And>n y. f n y \<noteq> 0 \<Longrightarrow> norm_class.norm (z - y) \<le> R"
    and target_support:
      "\<And>y. g y \<noteq> 0 \<Longrightarrow> norm_class.norm (z - y) \<le> R"
    and error_norm_tends:
      "((\<lambda>n. aim_complex_lp_norm b (\<lambda>x. f n x - g x))
        \<longlongrightarrow> 0) sequentially"
  shows "((\<lambda>n. slp_cauchy_transform orientation (f n) z)
    \<longlongrightarrow> slp_cauchy_transform orientation g z) sequentially"
proof -
  have b_positive: "0 < b"
    using exponent by linarith
  let ?complex_norm = "Real_Vector_Spaces.norm :: complex \<Rightarrow> real"
  have error_lp:
      "aim_complex_lp_on_plane b (\<lambda>x. f n x - g x)" for n
    by (rule aim_complex_lp_on_plane_diff[OF b_positive source_lp target_lp])
  let ?I = "\<lambda>n. integral\<^sup>L lborel
    (\<lambda>x. Real_Vector_Spaces.norm (f n x - g x) powr b)"
  have integral_nonnegative: "0 \<le> ?I n" for n
    by (rule Bochner_Integration.integral_nonneg) simp
  have error_norm_nonnegative:
      "0 \<le> aim_complex_lp_norm b (\<lambda>x. f n x - g x)" for n
    unfolding aim_complex_lp_norm_def by simp
  have powered_tends:
      "((\<lambda>n. aim_complex_lp_norm b (\<lambda>x. f n x - g x) powr b)
        \<longlongrightarrow> 0) sequentially"
  proof -
    have "((\<lambda>n. aim_complex_lp_norm b
        (\<lambda>x. f n x - g x) powr b) \<longlongrightarrow> 0 powr b)
        sequentially"
      by (rule tendsto_powr2[OF error_norm_tends tendsto_const])
        (use error_norm_nonnegative b_positive in auto)
    then show ?thesis
      using b_positive by simp
  qed
  have norm_power:
      "aim_complex_lp_norm b (\<lambda>x. f n x - g x) powr b = ?I n" for n
    unfolding aim_complex_lp_norm_def
    using b_positive integral_nonnegative[of n]
    by (simp add: powr_powr)
  have error_power_tends:
      "((\<lambda>n. integral\<^sup>L lborel
        (\<lambda>x. Real_Vector_Spaces.norm (f n x - g x) powr b))
        \<longlongrightarrow> 0)
        sequentially"
    using powered_tends by (simp only: norm_power)
  have error_support:
      "\<And>n y. f n y - g y \<noteq> 0 \<Longrightarrow>
        norm_class.norm (z - y) \<le> R"
  proof -
    fix n y
    assume difference_nonzero: "f n y - g y \<noteq> 0"
    have "f n y \<noteq> 0 \<or> g y \<noteq> 0"
      using difference_nonzero by auto
    then show "norm_class.norm (z - y) \<le> R"
      using source_support[of n y] target_support[of y] by blast
  qed
  have weighted_L1:
      "((\<lambda>n. \<integral>\<^sup>+y.
        ?complex_norm (slp_cauchy_integrand orientation
          (\<lambda>x. f n x - g x) z y) \<partial>lborel)
        \<longlongrightarrow> 0) sequentially"
    by (rule slp_cauchy_weighted_L1_tendsto_of_power_error[OF
          exponent radius_nonnegative error_lp error_support
          error_power_tends])
  have source_integrable:
      "slp_cauchy_integrable_at orientation (f n) z" for n
    using slp_cauchy_scaled_young_bound_on_bounded_support[OF
      exponent radius_nonnegative zero_less_one source_lp[of n]
      source_support[of n], where orientation=orientation]
    by blast
  have target_integrable:
      "slp_cauchy_integrable_at orientation g z"
    using slp_cauchy_scaled_young_bound_on_bounded_support[OF
      exponent radius_nonnegative zero_less_one target_lp target_support,
      where orientation=orientation]
    by blast
  show ?thesis
    by (rule slp_cauchy_transform_tendsto_of_weighted_L1[OF
          source_integrable target_integrable weighted_L1])
qed

end
