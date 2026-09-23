theory Inverse_Schrodinger_Lp_Cauchy_Local_Lp_Above_Two
  imports Inverse_Schrodinger_Lp_Cauchy_Local_Lp_Two
begin

section \<open>The reciprocal HLS source exponent\<close>

definition slp_hls_source_exponent :: "real \<Rightarrow> real" where
  "slp_hls_source_exponent s = 2 * s / (s + 2)"

lemma slp_hls_source_exponent_bounds:
  assumes s_lower: "2 < s"
  shows "1 < slp_hls_source_exponent s"
    and "slp_hls_source_exponent s < 2"
    and "slp_hls_source_exponent s \<le> s"
proof -
  have denominator_positive: "0 < s + 2"
    using s_lower by linarith
  show "1 < slp_hls_source_exponent s"
    unfolding slp_hls_source_exponent_def
    by (subst pos_less_divide_eq[OF denominator_positive])
       (use s_lower in simp)
  show "slp_hls_source_exponent s < 2"
    unfolding slp_hls_source_exponent_def
    by (subst pos_divide_less_eq[OF denominator_positive])
       (use s_lower in simp)
  have s_positive: "0 < s"
    using s_lower by linarith
  have "2 * s \<le> s * (s + 2)"
    using s_positive by (simp add: algebra_simps)
  then show "slp_hls_source_exponent s \<le> s"
    unfolding slp_hls_source_exponent_def
    by (subst pos_divide_le_eq[OF denominator_positive])
qed

lemma slp_hls_source_target_identity:
  assumes s_lower: "2 < s"
  shows "aim_hls_target_exponent (slp_hls_source_exponent s) = s"
proof -
  have s_nonzero: "s \<noteq> 0"
    using s_lower by linarith
  have denominator_nonzero: "s + 2 \<noteq> 0"
    using s_lower by linarith
  have source_identity:
    "slp_hls_source_exponent s = 2 * s / (s + 2)"
    by (simp add: slp_hls_source_exponent_def)
  show ?thesis
    unfolding aim_hls_target_exponent_def source_identity
    using s_nonzero denominator_nonzero
    by (simp add: divide_simps algebra_simps)
qed

section \<open>The local zero-order term above exponent two\<close>

context aim_planar_hls_cauchy
begin

theorem slp_both_cauchy_local_lp_above_two:
  assumes s_lower: "2 < (s::real)"
    and f_lp: "aim_complex_lp_on_plane s f"
    and f_support: "bounded {x. f x \<noteq> 0}"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
  shows "slp_complex_lp_on s X (slp_dbar_inverse f) \<and>
    slp_complex_lp_on s X (slp_partial_inverse f)"
proof -
  have source_lower: "1 < slp_hls_source_exponent s"
    and source_upper: "slp_hls_source_exponent s < 2"
    and source_le: "slp_hls_source_exponent s \<le> s"
    using slp_hls_source_exponent_bounds[OF s_lower] by auto
  have source_positive: "0 < slp_hls_source_exponent s"
    using source_lower by linarith
  have input_descent:
    "aim_complex_lp_on_plane (slp_hls_source_exponent s) f"
    by (rule aim_complex_lp_on_plane_mono_exponent_bounded_support[OF
          source_positive source_le f_support f_lp])
  have target_memberships:
    "slp_complex_lp_on
        (aim_hls_target_exponent (slp_hls_source_exponent s)) X
        (slp_dbar_inverse f) \<and>
      slp_complex_lp_on
        (aim_hls_target_exponent (slp_hls_source_exponent s)) X
        (slp_partial_inverse f)"
    using slp_both_cauchy_hls_sum_on_measurable source_lower source_upper
      input_descent X_measurable by blast
  show ?thesis
    using target_memberships slp_hls_source_target_identity[OF s_lower]
    by simp
qed

end

end
