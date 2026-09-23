theory Inverse_Schrodinger_Lp_Qstar_Near_Cutoff_HLS
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_010.Inverse_Schrodinger_Lp_Qstar_Near_Cutoff_Amplitude_Complex_Lp"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_010.Inverse_Schrodinger_Lp_Qstar_Oscillatory_Partial_HLS"
begin

section \<open>Explicit HLS estimate for the canonical near cutoff\<close>

context aim_planar_hls_cauchy
begin

theorem slp_qstar_near_cutoff_hls:
  "\<exists>C::real. 0 < C \<and>
    (\<forall>a tau delta c f.
      1 < a \<and> a < 2 \<and> 0 < delta \<and>
      aim_complex_lp_on_plane (aim_hls_target_exponent a) f
      \<longrightarrow>
      aim_complex_lp_on_plane (aim_hls_target_exponent a)
        (slp_partial_psi_inverse tau c
          (slp_global_cutoff.slp_near_cutoff_amplitude delta c f)) \<and>
      aim_complex_lp_norm (aim_hls_target_exponent a)
          (slp_partial_psi_inverse tau c
            (slp_global_cutoff.slp_near_cutoff_amplitude delta c f))
        \<le> C / ((a - 1) * (2 - a)) *
          ((2 * sqrt pi * delta) *
            aim_complex_lp_norm (aim_hls_target_exponent a) f))"
proof -
  obtain C::real where C_positive: "0 < C"
    and C_bound:
      "\<And>p tau c g.
        1 < p \<Longrightarrow> p < 2 \<Longrightarrow>
        aim_complex_lp_on_plane p g \<Longrightarrow>
        aim_complex_lp_on_plane (aim_hls_target_exponent p)
          (slp_partial_psi_inverse tau c g) \<and>
        aim_complex_lp_norm (aim_hls_target_exponent p)
            (slp_partial_psi_inverse tau c g)
          \<le> C / ((p - 1) * (2 - p)) * aim_complex_lp_norm p g"
    using slp_partial_psi_inverse_hls by blast
  have all_bound:
      "\<forall>a tau delta c f.
        1 < a \<and> a < 2 \<and> 0 < delta \<and>
        aim_complex_lp_on_plane (aim_hls_target_exponent a) f
        \<longrightarrow>
        aim_complex_lp_on_plane (aim_hls_target_exponent a)
          (slp_partial_psi_inverse tau c
            (slp_global_cutoff.slp_near_cutoff_amplitude delta c f)) \<and>
        aim_complex_lp_norm (aim_hls_target_exponent a)
            (slp_partial_psi_inverse tau c
              (slp_global_cutoff.slp_near_cutoff_amplitude delta c f))
          \<le> C / ((a - 1) * (2 - a)) *
            ((2 * sqrt pi * delta) *
              aim_complex_lp_norm (aim_hls_target_exponent a) f)"
  proof (intro allI impI)
    fix a tau delta :: real and c :: slp_point and f :: slp_scalar_field
    assume hypotheses:
      "1 < a \<and> a < 2 \<and> 0 < delta \<and>
        aim_complex_lp_on_plane (aim_hls_target_exponent a) f"
    have exponent_lower: "1 < a"
      and exponent_upper: "a < 2"
      and delta_positive: "0 < delta"
      and amplitude_lp:
        "aim_complex_lp_on_plane (aim_hls_target_exponent a) f"
      using hypotheses by blast+
    note near_data = slp_qstar_near_cutoff_amplitude_complex_Lp[
        OF exponent_lower exponent_upper delta_positive amplitude_lp]
    have hls_data:
        "aim_complex_lp_on_plane (aim_hls_target_exponent a)
            (slp_partial_psi_inverse tau c
              (slp_global_cutoff.slp_near_cutoff_amplitude delta c f)) \<and>
          aim_complex_lp_norm (aim_hls_target_exponent a)
              (slp_partial_psi_inverse tau c
                (slp_global_cutoff.slp_near_cutoff_amplitude delta c f))
            \<le> C / ((a - 1) * (2 - a)) *
              aim_complex_lp_norm a
                (slp_global_cutoff.slp_near_cutoff_amplitude delta c f)"
      by (rule C_bound[OF exponent_lower exponent_upper near_data(1)])
    have denominator_positive: "0 < (a - 1) * (2 - a)"
      by (rule mult_pos_pos) (use exponent_lower exponent_upper in linarith)+
    have coefficient_nonnegative:
        "0 \<le> C / ((a - 1) * (2 - a))"
      using C_positive denominator_positive by simp
    have propagated_bound:
        "C / ((a - 1) * (2 - a)) *
            aim_complex_lp_norm a
              (slp_global_cutoff.slp_near_cutoff_amplitude delta c f) \<le>
          C / ((a - 1) * (2 - a)) *
            ((2 * sqrt pi * delta) *
              aim_complex_lp_norm (aim_hls_target_exponent a) f)"
      by (rule mult_left_mono[OF near_data(2) coefficient_nonnegative])
    show
      "aim_complex_lp_on_plane (aim_hls_target_exponent a)
          (slp_partial_psi_inverse tau c
            (slp_global_cutoff.slp_near_cutoff_amplitude delta c f)) \<and>
        aim_complex_lp_norm (aim_hls_target_exponent a)
            (slp_partial_psi_inverse tau c
              (slp_global_cutoff.slp_near_cutoff_amplitude delta c f))
          \<le> C / ((a - 1) * (2 - a)) *
            ((2 * sqrt pi * delta) *
              aim_complex_lp_norm (aim_hls_target_exponent a) f)"
    proof
      show "aim_complex_lp_on_plane (aim_hls_target_exponent a)
          (slp_partial_psi_inverse tau c
            (slp_global_cutoff.slp_near_cutoff_amplitude delta c f))"
        by (rule conjunct1[OF hls_data])
      show "aim_complex_lp_norm (aim_hls_target_exponent a)
            (slp_partial_psi_inverse tau c
              (slp_global_cutoff.slp_near_cutoff_amplitude delta c f))
          \<le> C / ((a - 1) * (2 - a)) *
            ((2 * sqrt pi * delta) *
              aim_complex_lp_norm (aim_hls_target_exponent a) f)"
        by (rule order_trans[OF conjunct2[OF hls_data] propagated_bound])
    qed
  qed
  show ?thesis
    using C_positive all_bound by blast
qed

end

end
