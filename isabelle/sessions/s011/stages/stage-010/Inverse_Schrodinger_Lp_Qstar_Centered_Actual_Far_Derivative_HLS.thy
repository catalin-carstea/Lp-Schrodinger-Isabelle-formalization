theory Inverse_Schrodinger_Lp_Qstar_Centered_Actual_Far_Derivative_HLS
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_010.Inverse_Schrodinger_Lp_Oscillatory_Partial_AE_Congruence"
begin

section \<open>HLS estimate for the actual centered smooth far derivative\<close>

context slp_qstar_centered_three_term_hls_context
begin

theorem slp_qstar_centered_actual_far_derivative_hls:
  "\<exists>C::real. 0 < C \<and>
    (\<forall>a tau delta R f.
      1 < a \<and> a < 2 \<and> 0 < delta \<and> delta \<le> R \<and>
      slp_test_function_on UNIV f \<and>
      aim_complex_lp_on_plane (aim_hls_target_exponent a) f \<and>
      aim_complex_lp_on_plane a (slp_classical_wirtinger_partial f) \<and>
      (\<forall>y. f y \<noteq> 0 \<longrightarrow> norm y \<le> R)
      \<longrightarrow>
      aim_complex_lp_on_plane (aim_hls_target_exponent a)
        (slp_partial_psi_inverse tau 0
          (slp_classical_wirtinger_partial
            (slp_global_cutoff.slp_far_product delta 0 f))) \<and>
      aim_complex_lp_norm (aim_hls_target_exponent a)
          (slp_partial_psi_inverse tau 0
            (slp_classical_wirtinger_partial
              (slp_global_cutoff.slp_far_product delta 0 f)))
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
    and complete_hls:
      "\<And>a tau delta R f.
        1 < a \<Longrightarrow> a < 2 \<Longrightarrow> 0 < delta \<Longrightarrow>
        delta \<le> R \<Longrightarrow>
        aim_complex_lp_on_plane (aim_hls_target_exponent a) f \<Longrightarrow>
        aim_complex_lp_on_plane a (slp_classical_wirtinger_partial f) \<Longrightarrow>
        (\<And>y. f y \<noteq> 0 \<Longrightarrow> norm y \<le> R) \<Longrightarrow>
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
    using slp_qstar_centered_three_term_source_hls by blast
  have all_bound:
      "\<forall>a tau delta R f.
        1 < a \<and> a < 2 \<and> 0 < delta \<and> delta \<le> R \<and>
        slp_test_function_on UNIV f \<and>
        aim_complex_lp_on_plane (aim_hls_target_exponent a) f \<and>
        aim_complex_lp_on_plane a (slp_classical_wirtinger_partial f) \<and>
        (\<forall>y. f y \<noteq> 0 \<longrightarrow> norm y \<le> R)
        \<longrightarrow>
        aim_complex_lp_on_plane (aim_hls_target_exponent a)
          (slp_partial_psi_inverse tau 0
            (slp_classical_wirtinger_partial
              (slp_global_cutoff.slp_far_product delta 0 f))) \<and>
        aim_complex_lp_norm (aim_hls_target_exponent a)
            (slp_partial_psi_inverse tau 0
              (slp_classical_wirtinger_partial
                (slp_global_cutoff.slp_far_product delta 0 f)))
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
        slp_test_function_on UNIV f \<and>
        aim_complex_lp_on_plane (aim_hls_target_exponent a) f \<and>
        aim_complex_lp_on_plane a (slp_classical_wirtinger_partial f) \<and>
        (\<forall>y. f y \<noteq> 0 \<longrightarrow> norm y \<le> R)"
    have exponent_lower: "1 < a"
      and exponent_upper: "a < 2"
      and delta_positive: "0 < delta"
      and radius_lower: "delta \<le> R"
      and f_test: "slp_test_function_on UNIV f"
      and amplitude_lp:
        "aim_complex_lp_on_plane (aim_hls_target_exponent a) f"
      and amplitude_derivative_lp:
        "aim_complex_lp_on_plane a (slp_classical_wirtinger_partial f)"
      and amplitude_radius: "\<And>y. f y \<noteq> 0 \<Longrightarrow> norm y \<le> R"
      using hypotheses by blast+
    let ?actual = "slp_classical_wirtinger_partial
      (slp_global_cutoff.slp_far_product delta 0 f)"
    let ?complete = "\<lambda>y.
      slp_qstar_far_amplitude_derivative_source delta 0 f y -
      slp_qstar_centered_cutoff_partial_source delta f y -
      slp_qstar_centered_square_denominator_source delta f y"
    note source_data =
      slp_qstar_centered_three_term_source_input_complex_Lp[
        OF exponent_lower exponent_upper delta_positive radius_lower
          amplitude_lp amplitude_derivative_lp amplitude_radius]
    have complete_measurable: "?complete \<in> borel_measurable lborel"
      using source_data(1) unfolding aim_complex_lp_on_plane_def by blast
    have actual_eq_complete:
        "AE y in (lborel :: slp_point measure). ?actual y = ?complete y"
      by (rule slp_qstar_centered_far_derivative_source_decomposition_AE[
            OF delta_positive f_test])
    have actual_representation:
        "?actual = (\<lambda>y. if y = 0 then ?actual 0 else ?complete y)"
    proof (rule ext)
      fix y :: slp_point
      show "?actual y = (if y = 0 then ?actual 0 else ?complete y)"
      proof (cases "y = 0")
        case True
        then show ?thesis by simp
      next
        case False
        have away_from_center: "?actual y = ?complete y"
          by (rule slp_qstar_centered_far_derivative_source_decomposition[
                OF delta_positive f_test False])
        then show ?thesis using False by simp
      qed
    qed
    have patched_measurable:
        "(\<lambda>y. if y = 0 then ?actual 0 else ?complete y)
          \<in> borel_measurable lborel"
      using complete_measurable by measurable
    have actual_measurable: "?actual \<in> borel_measurable lborel"
      apply (subst actual_representation)
      by (rule patched_measurable)
    have output_eq:
        "slp_partial_psi_inverse tau 0 ?actual =
          slp_partial_psi_inverse tau 0 ?complete"
      by (rule slp_partial_psi_inverse_cong_AE[
            OF actual_measurable complete_measurable actual_eq_complete])
    have complete_output:
        "aim_complex_lp_on_plane (aim_hls_target_exponent a)
            (slp_partial_psi_inverse tau 0 ?complete) \<and>
          aim_complex_lp_norm (aim_hls_target_exponent a)
              (slp_partial_psi_inverse tau 0 ?complete)
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
      by (rule complete_hls[OF exponent_lower exponent_upper delta_positive
            radius_lower amplitude_lp amplitude_derivative_lp amplitude_radius])
    show
      "aim_complex_lp_on_plane (aim_hls_target_exponent a)
          (slp_partial_psi_inverse tau 0 ?actual) \<and>
        aim_complex_lp_norm (aim_hls_target_exponent a)
            (slp_partial_psi_inverse tau 0 ?actual)
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
      using complete_output output_eq by simp
  qed
  show ?thesis
    using C_positive all_bound by blast
qed

end

end
