theory Inverse_Schrodinger_Lp_Cauchy_HLS_Sum
  imports Inverse_Schrodinger_Lp_Cauchy_HLS_Both
begin

section \<open>The summed two-orientation HLS estimate\<close>

context aim_planar_hls_cauchy
begin

theorem slp_both_cauchy_hls_sum:
  "\<exists>K::real. 0 < K \<and>
    (\<forall>p f. 1 < p \<and> p < 2 \<and> aim_complex_lp_on_plane p f
      \<longrightarrow>
      aim_complex_lp_on_plane (aim_hls_target_exponent p)
          (slp_dbar_inverse f) \<and>
      aim_complex_lp_on_plane (aim_hls_target_exponent p)
          (slp_partial_inverse f) \<and>
      aim_complex_lp_norm (aim_hls_target_exponent p)
          (slp_partial_inverse f) +
        aim_complex_lp_norm (aim_hls_target_exponent p)
          (slp_dbar_inverse f)
        \<le> K / ((p - 1) * (2 - p)) * aim_complex_lp_norm p f)"
proof -
  obtain C::real where C_positive: "0 < C"
    and C_bound:
      "\<And>p f. 1 < p \<Longrightarrow> p < 2 \<Longrightarrow>
        aim_complex_lp_on_plane p f \<Longrightarrow>
        aim_complex_lp_on_plane (aim_hls_target_exponent p)
            (slp_dbar_inverse f) \<and>
        aim_complex_lp_on_plane (aim_hls_target_exponent p)
            (slp_partial_inverse f) \<and>
        aim_complex_lp_norm (aim_hls_target_exponent p)
            (slp_dbar_inverse f)
          \<le> C / ((p - 1) * (2 - p)) * aim_complex_lp_norm p f \<and>
        aim_complex_lp_norm (aim_hls_target_exponent p)
            (slp_partial_inverse f)
          \<le> C / ((p - 1) * (2 - p)) * aim_complex_lp_norm p f"
    using slp_both_cauchy_hls by blast
  have doubled_positive: "0 < 2 * C"
    using C_positive by simp
  have all_bound:
    "\<forall>p f. 1 < p \<and> p < 2 \<and> aim_complex_lp_on_plane p f
      \<longrightarrow>
      aim_complex_lp_on_plane (aim_hls_target_exponent p)
          (slp_dbar_inverse f) \<and>
      aim_complex_lp_on_plane (aim_hls_target_exponent p)
          (slp_partial_inverse f) \<and>
      aim_complex_lp_norm (aim_hls_target_exponent p)
          (slp_partial_inverse f) +
        aim_complex_lp_norm (aim_hls_target_exponent p)
          (slp_dbar_inverse f)
        \<le> (2 * C) / ((p - 1) * (2 - p)) * aim_complex_lp_norm p f"
  proof (intro allI impI)
    fix p f
    assume hypotheses:
      "1 < p \<and> p < 2 \<and> aim_complex_lp_on_plane p f"
    have both_result:
      "aim_complex_lp_on_plane (aim_hls_target_exponent p)
            (slp_dbar_inverse f) \<and>
        aim_complex_lp_on_plane (aim_hls_target_exponent p)
            (slp_partial_inverse f) \<and>
        aim_complex_lp_norm (aim_hls_target_exponent p)
            (slp_dbar_inverse f)
          \<le> C / ((p - 1) * (2 - p)) * aim_complex_lp_norm p f \<and>
        aim_complex_lp_norm (aim_hls_target_exponent p)
            (slp_partial_inverse f)
          \<le> C / ((p - 1) * (2 - p)) * aim_complex_lp_norm p f"
      by (rule C_bound) (use hypotheses in auto)
    have sum_bound:
      "aim_complex_lp_norm (aim_hls_target_exponent p)
          (slp_partial_inverse f) +
        aim_complex_lp_norm (aim_hls_target_exponent p)
          (slp_dbar_inverse f)
        \<le> 2 *
          (C / ((p - 1) * (2 - p)) * aim_complex_lp_norm p f)"
      using both_result by linarith
    have coefficient_identity:
      "2 * (C / ((p - 1) * (2 - p)) * aim_complex_lp_norm p f) =
        (2 * C) / ((p - 1) * (2 - p)) * aim_complex_lp_norm p f"
      by (simp add: algebra_simps)
    have normalized_sum_bound:
      "aim_complex_lp_norm (aim_hls_target_exponent p)
          (slp_partial_inverse f) +
        aim_complex_lp_norm (aim_hls_target_exponent p)
          (slp_dbar_inverse f)
        \<le> (2 * C) / ((p - 1) * (2 - p)) * aim_complex_lp_norm p f"
      using sum_bound coefficient_identity by linarith
    show "aim_complex_lp_on_plane (aim_hls_target_exponent p)
          (slp_dbar_inverse f) \<and>
      aim_complex_lp_on_plane (aim_hls_target_exponent p)
          (slp_partial_inverse f) \<and>
      aim_complex_lp_norm (aim_hls_target_exponent p)
          (slp_partial_inverse f) +
        aim_complex_lp_norm (aim_hls_target_exponent p)
          (slp_dbar_inverse f)
        \<le> (2 * C) / ((p - 1) * (2 - p)) * aim_complex_lp_norm p f"
      using both_result normalized_sum_bound by blast
  qed
  show ?thesis
    using doubled_positive all_bound by blast
qed

end

end
