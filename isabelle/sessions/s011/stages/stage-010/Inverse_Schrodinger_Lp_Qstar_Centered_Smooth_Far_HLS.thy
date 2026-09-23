theory Inverse_Schrodinger_Lp_Qstar_Centered_Smooth_Far_HLS
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_010.Inverse_Schrodinger_Lp_Qstar_Centered_Actual_Far_Derivative_HLS"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_010.Inverse_Schrodinger_Lp_Qstar_Smooth_Far_Operator_Complex_Lp"
begin

section \<open>Explicit HLS estimate for the centered smooth far operator\<close>

locale slp_qstar_centered_smooth_far_hls_context =
  slp_qstar_centered_three_term_hls_context +
  aim_planar_cauchy_test_left_inverse

context slp_qstar_centered_smooth_far_hls_context
begin

theorem slp_qstar_centered_smooth_far_hls:
  "\<exists>C::real. 0 < C \<and>
    (\<forall>a tau delta R f.
      1 < a \<and> a < 2 \<and> 0 < tau \<and> 0 < delta \<and>
      delta \<le> R \<and>
      slp_test_function_on UNIV f \<and>
      aim_complex_lp_on_plane (aim_hls_target_exponent a) f \<and>
      aim_complex_lp_on_plane a (slp_classical_wirtinger_partial f) \<and>
      (\<forall>y. f y \<noteq> 0 \<longrightarrow> norm y \<le> R)
      \<longrightarrow>
      aim_complex_lp_on_plane (aim_hls_target_exponent a)
        (slp_partial_psi_inverse tau 0
          (slp_global_far_cutoff_amplitude delta 0 f)) \<and>
      aim_complex_lp_norm (aim_hls_target_exponent a)
          (slp_partial_psi_inverse tau 0
            (slp_global_far_cutoff_amplitude delta 0 f))
        \<le> (1 / tau) *
          (4 *
            ((2 / delta) *
                aim_complex_lp_norm (aim_hls_target_exponent a) f +
              C / ((a - 1) * (2 - a)) *
                (4 *
                  (4 *
                    ((2 / delta) *
                        aim_complex_lp_norm a
                          (slp_classical_wirtinger_partial f) +
                      (slp_global_cutoff_L / delta) *
                        ((integral\<^sup>L lborel
                            (slp_squared_radial_annulus 1 2)) powr
                            (1 / 2) *
                          aim_complex_lp_norm
                            (aim_hls_target_exponent a) f)) +
                    (1 / delta) *
                      slp_qstar_annular_J2_unit_coefficient_mass powr
                        (1 / 2) *
                      aim_complex_lp_norm
                        (aim_hls_target_exponent a) f)))))"
proof -
  obtain C::real where C_positive: "0 < C"
    and derivative_hls:
      "\<And>a tau delta R f.
        1 < a \<Longrightarrow> a < 2 \<Longrightarrow> 0 < delta \<Longrightarrow>
        delta \<le> R \<Longrightarrow>
        slp_test_function_on UNIV f \<Longrightarrow>
        aim_complex_lp_on_plane (aim_hls_target_exponent a) f \<Longrightarrow>
        aim_complex_lp_on_plane a (slp_classical_wirtinger_partial f) \<Longrightarrow>
        (\<And>y. f y \<noteq> 0 \<Longrightarrow> norm y \<le> R) \<Longrightarrow>
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
    using slp_qstar_centered_actual_far_derivative_hls by blast
  have all_bound:
      "\<forall>a tau delta R f.
        1 < a \<and> a < 2 \<and> 0 < tau \<and> 0 < delta \<and>
        delta \<le> R \<and>
        slp_test_function_on UNIV f \<and>
        aim_complex_lp_on_plane (aim_hls_target_exponent a) f \<and>
        aim_complex_lp_on_plane a (slp_classical_wirtinger_partial f) \<and>
        (\<forall>y. f y \<noteq> 0 \<longrightarrow> norm y \<le> R)
        \<longrightarrow>
        aim_complex_lp_on_plane (aim_hls_target_exponent a)
          (slp_partial_psi_inverse tau 0
            (slp_global_far_cutoff_amplitude delta 0 f)) \<and>
        aim_complex_lp_norm (aim_hls_target_exponent a)
            (slp_partial_psi_inverse tau 0
              (slp_global_far_cutoff_amplitude delta 0 f))
          \<le> (1 / tau) *
            (4 *
              ((2 / delta) *
                  aim_complex_lp_norm (aim_hls_target_exponent a) f +
                C / ((a - 1) * (2 - a)) *
                  (4 *
                    (4 *
                      ((2 / delta) *
                          aim_complex_lp_norm a
                            (slp_classical_wirtinger_partial f) +
                        (slp_global_cutoff_L / delta) *
                          ((integral\<^sup>L lborel
                              (slp_squared_radial_annulus 1 2)) powr
                              (1 / 2) *
                            aim_complex_lp_norm
                              (aim_hls_target_exponent a) f)) +
                      (1 / delta) *
                        slp_qstar_annular_J2_unit_coefficient_mass powr
                          (1 / 2) *
                        aim_complex_lp_norm
                          (aim_hls_target_exponent a) f))))"
  proof (intro allI impI)
    fix a tau delta R :: real and f :: slp_scalar_field
    assume hypotheses:
      "1 < a \<and> a < 2 \<and> 0 < tau \<and> 0 < delta \<and>
        delta \<le> R \<and>
        slp_test_function_on UNIV f \<and>
        aim_complex_lp_on_plane (aim_hls_target_exponent a) f \<and>
        aim_complex_lp_on_plane a (slp_classical_wirtinger_partial f) \<and>
        (\<forall>y. f y \<noteq> 0 \<longrightarrow> norm y \<le> R)"
    have exponent_lower: "1 < a"
      and exponent_upper: "a < 2"
      and tau_positive: "0 < tau"
      and delta_positive: "0 < delta"
      and radius_lower: "delta \<le> R"
      and f_test: "slp_test_function_on UNIV f"
      and amplitude_lp:
        "aim_complex_lp_on_plane (aim_hls_target_exponent a) f"
      and amplitude_derivative_lp:
        "aim_complex_lp_on_plane a (slp_classical_wirtinger_partial f)"
      and amplitude_radius: "\<And>y. f y \<noteq> 0 \<Longrightarrow> norm y \<le> R"
      using hypotheses by blast+
    let ?q = "aim_hls_target_exponent a"
    let ?derivative = "slp_partial_psi_inverse tau 0
      (slp_classical_wirtinger_partial
        (slp_global_cutoff.slp_far_product delta 0 f))"
    let ?far = "slp_partial_psi_inverse tau 0
      (slp_global_far_cutoff_amplitude delta 0 f)"
    let ?H = "C / ((a - 1) * (2 - a)) *
      (4 *
        (4 *
          ((2 / delta) *
              aim_complex_lp_norm a
                (slp_classical_wirtinger_partial f) +
            (slp_global_cutoff_L / delta) *
              ((integral\<^sup>L lborel
                  (slp_squared_radial_annulus 1 2)) powr (1 / 2) *
                aim_complex_lp_norm ?q f)) +
          (1 / delta) *
            slp_qstar_annular_J2_unit_coefficient_mass powr (1 / 2) *
            aim_complex_lp_norm ?q f))"
    have q_above_two: "2 < ?q"
      by (rule slp_qstar_exponent_relations(1)[OF exponent_lower
            exponent_upper])
    have q_one_le: "1 \<le> ?q"
      using q_above_two by linarith
    have derivative_data:
        "aim_complex_lp_on_plane ?q ?derivative \<and>
          aim_complex_lp_norm ?q ?derivative \<le> ?H"
      by (rule derivative_hls[OF exponent_lower exponent_upper delta_positive
            radius_lower f_test amplitude_lp amplitude_derivative_lp
            amplitude_radius])
    have derivative_output_lp: "aim_complex_lp_on_plane ?q ?derivative"
      by (rule conjunct1[OF derivative_data])
    have derivative_norm_bound:
        "aim_complex_lp_norm ?q ?derivative \<le> ?H"
      by (rule conjunct2[OF derivative_data])
    note operator_data = slp_qstar_smooth_far_operator_complex_Lp[
        OF q_one_le tau_positive delta_positive f_test amplitude_lp
          derivative_output_lp]
    have sum_bound:
        "(2 / delta) * aim_complex_lp_norm ?q f +
            aim_complex_lp_norm ?q ?derivative \<le>
          (2 / delta) * aim_complex_lp_norm ?q f + ?H"
      by (rule add_left_mono[OF derivative_norm_bound])
    have four_sum_bound:
        "4 * ((2 / delta) * aim_complex_lp_norm ?q f +
            aim_complex_lp_norm ?q ?derivative) \<le>
          4 * ((2 / delta) * aim_complex_lp_norm ?q f + ?H)"
      by (rule mult_left_mono[OF sum_bound]) simp
    have scaled_bound:
        "(1 / tau) *
            (4 * ((2 / delta) * aim_complex_lp_norm ?q f +
              aim_complex_lp_norm ?q ?derivative)) \<le>
          (1 / tau) *
            (4 * ((2 / delta) * aim_complex_lp_norm ?q f + ?H))"
      by (rule mult_left_mono[OF four_sum_bound])
        (use tau_positive in simp)
    show
      "aim_complex_lp_on_plane ?q ?far \<and>
        aim_complex_lp_norm ?q ?far \<le>
          (1 / tau) *
            (4 * ((2 / delta) * aim_complex_lp_norm ?q f + ?H))"
    proof
      show "aim_complex_lp_on_plane ?q ?far"
        by (rule operator_data(1))
      show "aim_complex_lp_norm ?q ?far \<le>
          (1 / tau) *
            (4 * ((2 / delta) * aim_complex_lp_norm ?q f + ?H))"
        by (rule order_trans[OF operator_data(2) scaled_bound])
    qed
  qed
  show ?thesis
    using C_positive all_bound by blast
qed

end

end
