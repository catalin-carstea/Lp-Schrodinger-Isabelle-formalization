theory Inverse_Schrodinger_Lp_Qstar_Far_Amplitude_Derivative_HLS
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_010.Inverse_Schrodinger_Lp_Qstar_Far_Amplitude_Derivative_Source"
begin

section \<open>The HLS output bound for the far amplitude derivative\<close>

context aim_planar_hls_cauchy
begin

theorem slp_qstar_far_amplitude_derivative_hls:
  "\<exists>C::real. 0 < C \<and>
    (\<forall>a tau delta c f.
      1 < a \<and> a < 2 \<and> 0 < delta \<and>
      aim_complex_lp_on_plane a (slp_classical_wirtinger_partial f)
      \<longrightarrow>
      aim_complex_lp_on_plane (aim_hls_target_exponent a)
        (slp_partial_psi_inverse tau c
          (slp_qstar_far_amplitude_derivative_source delta c f)) \<and>
      aim_complex_lp_norm (aim_hls_target_exponent a)
          (slp_partial_psi_inverse tau c
            (slp_qstar_far_amplitude_derivative_source delta c f))
        \<le> C / ((a - 1) * (2 - a)) *
          ((2 / delta) *
            aim_complex_lp_norm a (slp_classical_wirtinger_partial f)))"
proof -
  obtain C::real where C_positive: "0 < C"
    and hls_bound:
      "\<And>p tau c g. 1 < p \<Longrightarrow> p < 2 \<Longrightarrow>
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
        aim_complex_lp_on_plane a (slp_classical_wirtinger_partial f)
        \<longrightarrow>
        aim_complex_lp_on_plane (aim_hls_target_exponent a)
          (slp_partial_psi_inverse tau c
            (slp_qstar_far_amplitude_derivative_source delta c f)) \<and>
        aim_complex_lp_norm (aim_hls_target_exponent a)
            (slp_partial_psi_inverse tau c
              (slp_qstar_far_amplitude_derivative_source delta c f))
          \<le> C / ((a - 1) * (2 - a)) *
            ((2 / delta) *
              aim_complex_lp_norm a (slp_classical_wirtinger_partial f))"
  proof (intro allI impI)
    fix a tau delta :: real and c :: slp_point and f :: slp_scalar_field
    assume hypotheses:
      "1 < a \<and> a < 2 \<and> 0 < delta \<and>
        aim_complex_lp_on_plane a (slp_classical_wirtinger_partial f)"
    have exponent_lower: "1 < a" and exponent_upper: "a < 2"
      and delta_positive: "0 < delta"
      and derivative_lp:
        "aim_complex_lp_on_plane a (slp_classical_wirtinger_partial f)"
      using hypotheses by blast+
    have exponent_positive: "0 < a"
      using exponent_lower by linarith
    let ?g = "slp_qstar_far_amplitude_derivative_source delta c f"
    have source_lp: "aim_complex_lp_on_plane a ?g"
      by (rule slp_qstar_far_amplitude_derivative_source_complex_Lp(1)[OF
            exponent_positive delta_positive derivative_lp])
    have source_norm:
        "aim_complex_lp_norm a ?g \<le>
          (2 / delta) *
            aim_complex_lp_norm a (slp_classical_wirtinger_partial f)"
      by (rule slp_qstar_far_amplitude_derivative_source_complex_Lp(2)[OF
            exponent_positive delta_positive derivative_lp])
    have hls_data:
        "aim_complex_lp_on_plane (aim_hls_target_exponent a)
            (slp_partial_psi_inverse tau c ?g) \<and>
          aim_complex_lp_norm (aim_hls_target_exponent a)
              (slp_partial_psi_inverse tau c ?g)
            \<le> C / ((a - 1) * (2 - a)) * aim_complex_lp_norm a ?g"
      by (rule hls_bound[OF exponent_lower exponent_upper source_lp])
    have output_lp:
        "aim_complex_lp_on_plane (aim_hls_target_exponent a)
          (slp_partial_psi_inverse tau c ?g)"
      using hls_data by blast
    have output_norm:
        "aim_complex_lp_norm (aim_hls_target_exponent a)
            (slp_partial_psi_inverse tau c ?g)
          \<le> C / ((a - 1) * (2 - a)) * aim_complex_lp_norm a ?g"
      using hls_data by blast
    have denominator_positive: "0 < (a - 1) * (2 - a)"
      by (rule mult_pos_pos) (use exponent_lower exponent_upper in linarith)+
    have hls_factor_nonnegative:
        "0 \<le> C / ((a - 1) * (2 - a))"
      using C_positive denominator_positive by simp
    have scaled_source:
        "C / ((a - 1) * (2 - a)) * aim_complex_lp_norm a ?g \<le>
          C / ((a - 1) * (2 - a)) *
            ((2 / delta) *
              aim_complex_lp_norm a (slp_classical_wirtinger_partial f))"
      by (rule mult_left_mono[OF source_norm hls_factor_nonnegative])
    have final_norm:
        "aim_complex_lp_norm (aim_hls_target_exponent a)
            (slp_partial_psi_inverse tau c ?g)
          \<le> C / ((a - 1) * (2 - a)) *
            ((2 / delta) *
              aim_complex_lp_norm a (slp_classical_wirtinger_partial f))"
      by (rule order_trans[OF output_norm scaled_source])
    show "aim_complex_lp_on_plane (aim_hls_target_exponent a)
          (slp_partial_psi_inverse tau c ?g) \<and>
        aim_complex_lp_norm (aim_hls_target_exponent a)
            (slp_partial_psi_inverse tau c ?g)
          \<le> C / ((a - 1) * (2 - a)) *
            ((2 / delta) *
              aim_complex_lp_norm a (slp_classical_wirtinger_partial f))"
      by (rule conjI[OF output_lp final_norm])
  qed
  show ?thesis
    using C_positive all_bound by blast
qed

end

end
