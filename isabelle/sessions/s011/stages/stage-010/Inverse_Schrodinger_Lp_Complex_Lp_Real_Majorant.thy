theory Inverse_Schrodinger_Lp_Complex_Lp_Real_Majorant
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_010.Inverse_Schrodinger_Lp_Qstar_Centered_Three_Term_Source_Decomposition"
begin

section \<open>Complex Lp fields dominated by real majorants\<close>

theorem slp_complex_lp_real_majorant:
  fixes F :: slp_scalar_field
    and M :: "slp_point \<Rightarrow> real"
  assumes exponent_positive: "0 < p"
    and field_measurable: "F \<in> borel_measurable lborel"
    and majorant_lp: "aim_real_lp_on_plane p M"
    and pointwise_bound: "AE x in lborel. norm (F x) \<le> M x"
  shows field_lp: "aim_complex_lp_on_plane p F"
    and field_norm_bound:
      "aim_complex_lp_norm p F \<le> aim_real_lp_norm p M"
proof -
  let ?u = "\<lambda>x. norm (F x)"
  have field_norm_measurable: "?u \<in> borel_measurable lborel"
    using field_measurable by measurable
  have field_norm_nonnegative: "AE x in lborel. 0 \<le> ?u x"
    by simp
  have field_norm_lp: "aim_real_lp_on_plane p ?u"
    by (rule slp_nonnegative_real_lp_mono(1)[OF exponent_positive
          field_norm_measurable majorant_lp field_norm_nonnegative
          pointwise_bound])
  have real_norm_bound:
      "aim_real_lp_norm p ?u \<le> aim_real_lp_norm p M"
    by (rule slp_nonnegative_real_lp_mono(2)[OF exponent_positive
          field_norm_measurable majorant_lp field_norm_nonnegative
          pointwise_bound])
  have field_power_integrable:
      "integrable lborel (\<lambda>x. norm (F x) powr p)"
    using field_norm_lp unfolding aim_real_lp_on_plane_def by simp
  show "aim_complex_lp_on_plane p F"
    unfolding aim_complex_lp_on_plane_def
    using field_measurable field_power_integrable by blast
  have norm_identity:
      "aim_complex_lp_norm p F = aim_real_lp_norm p ?u"
    unfolding aim_complex_lp_norm_def aim_real_lp_norm_def by simp
  show "aim_complex_lp_norm p F \<le> aim_real_lp_norm p M"
    unfolding norm_identity by (rule real_norm_bound)
qed

end
