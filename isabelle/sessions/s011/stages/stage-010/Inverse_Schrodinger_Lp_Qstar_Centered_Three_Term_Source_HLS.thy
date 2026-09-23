theory Inverse_Schrodinger_Lp_Qstar_Centered_Three_Term_Source_HLS
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_010.Inverse_Schrodinger_Lp_Qstar_Centered_Three_Term_Source_Input_Lp"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_010.Inverse_Schrodinger_Lp_Qstar_Oscillatory_Partial_HLS"
begin

section \<open>One HLS application to the complete centered derivative source\<close>

locale slp_qstar_centered_three_term_hls_context =
  aim_planar_hls_cauchy + aim_planar_riesz_hls

context slp_qstar_centered_three_term_hls_context
begin

theorem slp_qstar_centered_three_term_source_hls:
  "\<exists>C::real. 0 < C \<and>
    (\<forall>a tau delta R f.
      1 < a \<and> a < 2 \<and> 0 < delta \<and> delta \<le> R \<and>
      aim_complex_lp_on_plane (aim_hls_target_exponent a) f \<and>
      aim_complex_lp_on_plane a (slp_classical_wirtinger_partial f) \<and>
      (\<forall>y. f y \<noteq> 0 \<longrightarrow> norm y \<le> R)
      \<longrightarrow>
      aim_complex_lp_on_plane (aim_hls_target_exponent a)
        (slp_partial_psi_inverse tau 0
          (\<lambda>y.
            slp_qstar_far_amplitude_derivative_source delta 0 f y -
            slp_qstar_centered_cutoff_partial_source delta f y -
            slp_qstar_centered_square_denominator_source delta f y)) \<and>
      aim_complex_lp_norm (aim_hls_target_exponent a)
          (slp_partial_psi_inverse tau 0
            (\<lambda>y.
              slp_qstar_far_amplitude_derivative_source delta 0 f y -
              slp_qstar_centered_cutoff_partial_source delta f y -
              slp_qstar_centered_square_denominator_source delta f y))
        \<le> C / ((a - 1) * (2 - a)) *
          (4 *
            (4 *
              ((2 / delta) *
                  aim_complex_lp_norm a
                    (slp_classical_wirtinger_partial f) +
                (slp_global_cutoff_L / delta) *
                  ((integral\<^sup>L lborel
                      (slp_squared_radial_annulus 1 2)) powr (1 / 2) *
                    aim_complex_lp_norm (aim_hls_target_exponent a) f)) +
              (1 / delta) *
                slp_qstar_annular_J2_unit_coefficient_mass powr (1 / 2) *
                aim_complex_lp_norm (aim_hls_target_exponent a) f)))"
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
      "\<forall>a tau delta R f.
        1 < a \<and> a < 2 \<and> 0 < delta \<and> delta \<le> R \<and>
        aim_complex_lp_on_plane (aim_hls_target_exponent a) f \<and>
        aim_complex_lp_on_plane a (slp_classical_wirtinger_partial f) \<and>
        (\<forall>y. f y \<noteq> 0 \<longrightarrow> norm y \<le> R)
        \<longrightarrow>
        aim_complex_lp_on_plane (aim_hls_target_exponent a)
          (slp_partial_psi_inverse tau 0
            (\<lambda>y.
              slp_qstar_far_amplitude_derivative_source delta 0 f y -
              slp_qstar_centered_cutoff_partial_source delta f y -
              slp_qstar_centered_square_denominator_source delta f y)) \<and>
        aim_complex_lp_norm (aim_hls_target_exponent a)
            (slp_partial_psi_inverse tau 0
              (\<lambda>y.
                slp_qstar_far_amplitude_derivative_source delta 0 f y -
                slp_qstar_centered_cutoff_partial_source delta f y -
                slp_qstar_centered_square_denominator_source delta f y))
          \<le> C / ((a - 1) * (2 - a)) *
            (4 *
              (4 *
                ((2 / delta) *
                    aim_complex_lp_norm a
                      (slp_classical_wirtinger_partial f) +
                  (slp_global_cutoff_L / delta) *
                    ((integral\<^sup>L lborel
                        (slp_squared_radial_annulus 1 2)) powr (1 / 2) *
                      aim_complex_lp_norm (aim_hls_target_exponent a) f)) +
                (1 / delta) *
                  slp_qstar_annular_J2_unit_coefficient_mass powr (1 / 2) *
                  aim_complex_lp_norm (aim_hls_target_exponent a) f))"
  proof (intro allI impI)
    fix a tau delta R :: real and f :: slp_scalar_field
    assume hypotheses:
      "1 < a \<and> a < 2 \<and> 0 < delta \<and> delta \<le> R \<and>
        aim_complex_lp_on_plane (aim_hls_target_exponent a) f \<and>
        aim_complex_lp_on_plane a (slp_classical_wirtinger_partial f) \<and>
        (\<forall>y. f y \<noteq> 0 \<longrightarrow> norm y \<le> R)"
    have exponent_lower: "1 < a"
      and exponent_upper: "a < 2"
      and delta_positive: "0 < delta"
      and radius_lower: "delta \<le> R"
      and amplitude_lp:
        "aim_complex_lp_on_plane (aim_hls_target_exponent a) f"
      and amplitude_derivative_lp:
        "aim_complex_lp_on_plane a (slp_classical_wirtinger_partial f)"
      and amplitude_radius: "\<And>y. f y \<noteq> 0 \<Longrightarrow> norm y \<le> R"
      using hypotheses by blast+
    let ?g = "\<lambda>y.
      slp_qstar_far_amplitude_derivative_source delta 0 f y -
      slp_qstar_centered_cutoff_partial_source delta f y -
      slp_qstar_centered_square_denominator_source delta f y"
    note source_data = slp_qstar_centered_three_term_source_input_complex_Lp[
      OF exponent_lower exponent_upper delta_positive radius_lower
        amplitude_lp amplitude_derivative_lp amplitude_radius]
    have hls_data:
        "aim_complex_lp_on_plane (aim_hls_target_exponent a)
            (slp_partial_psi_inverse tau 0 ?g) \<and>
          aim_complex_lp_norm (aim_hls_target_exponent a)
              (slp_partial_psi_inverse tau 0 ?g)
            \<le> C / ((a - 1) * (2 - a)) * aim_complex_lp_norm a ?g"
      by (rule hls_bound[OF exponent_lower exponent_upper source_data(1)])
    have denominator_positive: "0 < (a - 1) * (2 - a)"
      by (rule mult_pos_pos) (use exponent_lower exponent_upper in linarith)+
    have hls_factor_nonnegative:
        "0 \<le> C / ((a - 1) * (2 - a))"
      using C_positive denominator_positive by simp
    have scaled_source:
        "C / ((a - 1) * (2 - a)) * aim_complex_lp_norm a ?g
          \<le> C / ((a - 1) * (2 - a)) *
            (4 *
              (4 *
                ((2 / delta) *
                    aim_complex_lp_norm a
                      (slp_classical_wirtinger_partial f) +
                  (slp_global_cutoff_L / delta) *
                    ((integral\<^sup>L lborel
                        (slp_squared_radial_annulus 1 2)) powr (1 / 2) *
                      aim_complex_lp_norm (aim_hls_target_exponent a) f)) +
                (1 / delta) *
                  slp_qstar_annular_J2_unit_coefficient_mass powr (1 / 2) *
                  aim_complex_lp_norm (aim_hls_target_exponent a) f))"
      by (rule mult_left_mono[OF source_data(2) hls_factor_nonnegative])
    have final_norm:
        "aim_complex_lp_norm (aim_hls_target_exponent a)
            (slp_partial_psi_inverse tau 0 ?g)
          \<le> C / ((a - 1) * (2 - a)) *
            (4 *
              (4 *
                ((2 / delta) *
                    aim_complex_lp_norm a
                      (slp_classical_wirtinger_partial f) +
                  (slp_global_cutoff_L / delta) *
                    ((integral\<^sup>L lborel
                        (slp_squared_radial_annulus 1 2)) powr (1 / 2) *
                      aim_complex_lp_norm (aim_hls_target_exponent a) f)) +
                (1 / delta) *
                  slp_qstar_annular_J2_unit_coefficient_mass powr (1 / 2) *
                  aim_complex_lp_norm (aim_hls_target_exponent a) f))"
      by (rule order_trans[OF hls_data[THEN conjunct2] scaled_source])
    show "aim_complex_lp_on_plane (aim_hls_target_exponent a)
          (slp_partial_psi_inverse tau 0 ?g) \<and>
        aim_complex_lp_norm (aim_hls_target_exponent a)
            (slp_partial_psi_inverse tau 0 ?g)
          \<le> C / ((a - 1) * (2 - a)) *
            (4 *
              (4 *
                ((2 / delta) *
                    aim_complex_lp_norm a
                      (slp_classical_wirtinger_partial f) +
                  (slp_global_cutoff_L / delta) *
                    ((integral\<^sup>L lborel
                        (slp_squared_radial_annulus 1 2)) powr (1 / 2) *
                      aim_complex_lp_norm (aim_hls_target_exponent a) f)) +
                (1 / delta) *
                  slp_qstar_annular_J2_unit_coefficient_mass powr (1 / 2) *
                  aim_complex_lp_norm (aim_hls_target_exponent a) f))"
      by (rule conjI[OF hls_data[THEN conjunct1] final_norm])
  qed
  show ?thesis
    using C_positive all_bound by blast
qed

end

end
