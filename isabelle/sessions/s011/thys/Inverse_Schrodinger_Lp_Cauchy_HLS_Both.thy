theory Inverse_Schrodinger_Lp_Cauchy_HLS_Both
  imports Inverse_Schrodinger_Lp_Cauchy_HLS_Conjugate
begin

section \<open>A common HLS constant for both Cauchy orientations\<close>

context aim_planar_hls_cauchy
begin

theorem slp_both_cauchy_hls:
  "\<exists>C::real. 0 < C \<and>
    (\<forall>p f. 1 < p \<and> p < 2 \<and> aim_complex_lp_on_plane p f
      \<longrightarrow>
      aim_complex_lp_on_plane (aim_hls_target_exponent p)
          (slp_dbar_inverse f) \<and>
      aim_complex_lp_on_plane (aim_hls_target_exponent p)
          (slp_partial_inverse f) \<and>
      aim_complex_lp_norm (aim_hls_target_exponent p)
          (slp_dbar_inverse f)
        \<le> C / ((p - 1) * (2 - p)) * aim_complex_lp_norm p f \<and>
      aim_complex_lp_norm (aim_hls_target_exponent p)
          (slp_partial_inverse f)
        \<le> C / ((p - 1) * (2 - p)) * aim_complex_lp_norm p f)"
proof -
  obtain C::real where C_positive: "0 < C"
    and C_bound:
      "\<And>p f. 1 < p \<Longrightarrow> p < 2 \<Longrightarrow>
        aim_complex_lp_on_plane p f \<Longrightarrow>
        aim_complex_lp_on_plane (aim_hls_target_exponent p)
            (slp_dbar_inverse f) \<and>
        aim_complex_lp_norm (aim_hls_target_exponent p)
            (slp_dbar_inverse f)
          \<le> C / ((p - 1) * (2 - p)) * aim_complex_lp_norm p f"
    using slp_dbar_inverse_hls by blast
  have all_bound:
    "\<forall>p f. 1 < p \<and> p < 2 \<and> aim_complex_lp_on_plane p f
      \<longrightarrow>
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
  proof (intro allI impI)
    fix p f
    assume hypotheses:
      "1 < p \<and> p < 2 \<and> aim_complex_lp_on_plane p f"
    have dbar_result:
      "aim_complex_lp_on_plane (aim_hls_target_exponent p)
          (slp_dbar_inverse f) \<and>
       aim_complex_lp_norm (aim_hls_target_exponent p)
          (slp_dbar_inverse f)
        \<le> C / ((p - 1) * (2 - p)) * aim_complex_lp_norm p f"
      by (rule C_bound) (use hypotheses in auto)
    have conjugate_result:
      "aim_complex_lp_on_plane (aim_hls_target_exponent p)
          (slp_dbar_inverse (\<lambda>y. cnj (f y))) \<and>
       aim_complex_lp_norm (aim_hls_target_exponent p)
          (slp_dbar_inverse (\<lambda>y. cnj (f y)))
        \<le> C / ((p - 1) * (2 - p)) *
          aim_complex_lp_norm p (\<lambda>y. cnj (f y))"
      by (rule C_bound) (use hypotheses in auto)
    have partial_result:
      "aim_complex_lp_on_plane (aim_hls_target_exponent p)
          (slp_partial_inverse f) \<and>
       aim_complex_lp_norm (aim_hls_target_exponent p)
          (slp_partial_inverse f)
        \<le> C / ((p - 1) * (2 - p)) * aim_complex_lp_norm p f"
      using conjugate_result
      by (simp only: slp_partial_inverse_via_dbar_conjugate
          aim_complex_lp_on_plane_cnj_iff aim_complex_lp_norm_cnj)
    show "aim_complex_lp_on_plane (aim_hls_target_exponent p)
          (slp_dbar_inverse f) \<and>
      aim_complex_lp_on_plane (aim_hls_target_exponent p)
          (slp_partial_inverse f) \<and>
      aim_complex_lp_norm (aim_hls_target_exponent p)
          (slp_dbar_inverse f)
        \<le> C / ((p - 1) * (2 - p)) * aim_complex_lp_norm p f \<and>
      aim_complex_lp_norm (aim_hls_target_exponent p)
          (slp_partial_inverse f)
        \<le> C / ((p - 1) * (2 - p)) * aim_complex_lp_norm p f"
      using dbar_result partial_result by blast
  qed
  show ?thesis
    using C_positive all_bound by blast
qed

end

end
