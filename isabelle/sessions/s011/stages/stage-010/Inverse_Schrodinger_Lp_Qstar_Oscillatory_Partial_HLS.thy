theory Inverse_Schrodinger_Lp_Qstar_Oscillatory_Partial_HLS
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_010.Inverse_Schrodinger_Lp_Qstar_Cutoff_Partial_Complex_Lp"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Cauchy_HLS_Both"
begin

section \<open>The planar HLS bound for the oscillatory partial-Cauchy operator\<close>

context aim_planar_hls_cauchy
begin

theorem slp_partial_psi_inverse_hls:
  "\<exists>C::real. 0 < C \<and>
    (\<forall>p tau c f. 1 < p \<and> p < 2 \<and> aim_complex_lp_on_plane p f
      \<longrightarrow>
      aim_complex_lp_on_plane (aim_hls_target_exponent p)
          (slp_partial_psi_inverse tau c f) \<and>
      aim_complex_lp_norm (aim_hls_target_exponent p)
          (slp_partial_psi_inverse tau c f)
        \<le> C / ((p - 1) * (2 - p)) * aim_complex_lp_norm p f)"
proof -
  obtain C::real where C_positive: "0 < C"
    and C_bound:
      "\<And>p f. 1 < p \<Longrightarrow> p < 2 \<Longrightarrow>
        aim_complex_lp_on_plane p f \<Longrightarrow>
        aim_complex_lp_on_plane (aim_hls_target_exponent p)
            (slp_partial_inverse f) \<and>
        aim_complex_lp_norm (aim_hls_target_exponent p)
            (slp_partial_inverse f)
          \<le> C / ((p - 1) * (2 - p)) * aim_complex_lp_norm p f"
    using slp_both_cauchy_hls by blast
  have all_bound:
      "\<forall>p tau c f. 1 < p \<and> p < 2 \<and> aim_complex_lp_on_plane p f
        \<longrightarrow>
        aim_complex_lp_on_plane (aim_hls_target_exponent p)
            (slp_partial_psi_inverse tau c f) \<and>
        aim_complex_lp_norm (aim_hls_target_exponent p)
            (slp_partial_psi_inverse tau c f)
          \<le> C / ((p - 1) * (2 - p)) * aim_complex_lp_norm p f"
  proof (intro allI impI)
    fix p tau c f
    assume hypotheses:
      "1 < p \<and> p < 2 \<and> aim_complex_lp_on_plane p f"
    have modulated_lp:
        "aim_complex_lp_on_plane p
          (slp_oscillatory_modulation tau c f)"
      using hypotheses by simp
    have transferred:
        "aim_complex_lp_on_plane (aim_hls_target_exponent p)
            (slp_partial_inverse
              (slp_oscillatory_modulation tau c f)) \<and>
          aim_complex_lp_norm (aim_hls_target_exponent p)
              (slp_partial_inverse
                (slp_oscillatory_modulation tau c f))
            \<le> C / ((p - 1) * (2 - p)) *
              aim_complex_lp_norm p
                (slp_oscillatory_modulation tau c f)"
      by (rule C_bound) (use hypotheses modulated_lp in auto)
    show "aim_complex_lp_on_plane (aim_hls_target_exponent p)
          (slp_partial_psi_inverse tau c f) \<and>
        aim_complex_lp_norm (aim_hls_target_exponent p)
            (slp_partial_psi_inverse tau c f)
          \<le> C / ((p - 1) * (2 - p)) * aim_complex_lp_norm p f"
      using transferred
      unfolding slp_partial_psi_inverse_def
      by (simp only: slp_oscillatory_modulation_lp_norm)
  qed
  show ?thesis
    using C_positive all_bound by blast
qed

end

end
