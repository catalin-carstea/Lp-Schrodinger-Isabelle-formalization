theory Inverse_Schrodinger_Lp_Qstar_Centered_Smooth_Total_HLS
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_010.Inverse_Schrodinger_Lp_Qstar_Smooth_Near_Far_Operator_Split"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_010.Inverse_Schrodinger_Lp_Qstar_Centered_Smooth_Far_HLS"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_010.Inverse_Schrodinger_Lp_Qstar_Near_Cutoff_HLS"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_010.Inverse_Schrodinger_Lp_Complex_Lp_Coarse_Triangle"
begin

section \<open>Combined centered smooth near/far estimate\<close>

context slp_qstar_centered_smooth_far_hls_context
begin

theorem slp_qstar_centered_smooth_total_hls:
  "\<exists>C_near C_far::real. 0 < C_near \<and> 0 < C_far \<and>
    (\<forall>a tau delta R f.
      1 < a \<and> a < 2 \<and> 0 < tau \<and> 0 < delta \<and>
      delta \<le> R \<and>
      slp_test_function_on UNIV f \<and>
      aim_complex_lp_on_plane (aim_hls_target_exponent a) f \<and>
      aim_complex_lp_on_plane a (slp_classical_wirtinger_partial f) \<and>
      (\<forall>y. f y \<noteq> 0 \<longrightarrow> norm y \<le> R)
      \<longrightarrow>
      aim_complex_lp_on_plane (aim_hls_target_exponent a)
        (slp_partial_psi_inverse tau 0 f) \<and>
      aim_complex_lp_norm (aim_hls_target_exponent a)
          (slp_partial_psi_inverse tau 0 f)
        \<le> 4 *
          (C_near / ((a - 1) * (2 - a)) *
              ((2 * sqrt pi * delta) *
                aim_complex_lp_norm (aim_hls_target_exponent a) f) +
            (1 / tau) *
              (4 *
                ((2 / delta) *
                    aim_complex_lp_norm (aim_hls_target_exponent a) f +
                  C_far / ((a - 1) * (2 - a)) *
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
                            (aim_hls_target_exponent a) f))))))"
proof -
  obtain C_near::real where C_near_positive: "0 < C_near"
    and near_bound:
      "\<And>a tau delta c f.
        1 < a \<Longrightarrow> a < 2 \<Longrightarrow> 0 < delta \<Longrightarrow>
        aim_complex_lp_on_plane (aim_hls_target_exponent a) f \<Longrightarrow>
        aim_complex_lp_on_plane (aim_hls_target_exponent a)
          (slp_partial_psi_inverse tau c
            (slp_global_cutoff.slp_near_cutoff_amplitude delta c f)) \<and>
        aim_complex_lp_norm (aim_hls_target_exponent a)
            (slp_partial_psi_inverse tau c
              (slp_global_cutoff.slp_near_cutoff_amplitude delta c f))
          \<le> C_near / ((a - 1) * (2 - a)) *
            ((2 * sqrt pi * delta) *
              aim_complex_lp_norm (aim_hls_target_exponent a) f)"
    using slp_qstar_near_cutoff_hls by blast
  obtain C_far::real where C_far_positive: "0 < C_far"
    and far_bound:
      "\<And>a tau delta R f.
        1 < a \<Longrightarrow> a < 2 \<Longrightarrow> 0 < tau \<Longrightarrow>
        0 < delta \<Longrightarrow> delta \<le> R \<Longrightarrow>
        slp_test_function_on UNIV f \<Longrightarrow>
        aim_complex_lp_on_plane (aim_hls_target_exponent a) f \<Longrightarrow>
        aim_complex_lp_on_plane a (slp_classical_wirtinger_partial f) \<Longrightarrow>
        (\<And>y. f y \<noteq> 0 \<Longrightarrow> norm y \<le> R) \<Longrightarrow>
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
                C_far / ((a - 1) * (2 - a)) *
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
    using slp_qstar_centered_smooth_far_hls by blast
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
          (slp_partial_psi_inverse tau 0 f) \<and>
        aim_complex_lp_norm (aim_hls_target_exponent a)
            (slp_partial_psi_inverse tau 0 f)
          \<le> 4 *
            (C_near / ((a - 1) * (2 - a)) *
                ((2 * sqrt pi * delta) *
                  aim_complex_lp_norm (aim_hls_target_exponent a) f) +
              (1 / tau) *
                (4 *
                  ((2 / delta) *
                      aim_complex_lp_norm (aim_hls_target_exponent a) f +
                    C_far / ((a - 1) * (2 - a)) *
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
  proof (intro allI impI)
    fix a tau delta R :: real and f :: slp_scalar_field
    assume hypotheses:
      "1 < a \<and> a < 2 \<and> 0 < tau \<and> 0 < delta \<and>
        delta \<le> R \<and>
        slp_test_function_on UNIV f \<and>
        aim_complex_lp_on_plane (aim_hls_target_exponent a) f \<and>
        aim_complex_lp_on_plane a (slp_classical_wirtinger_partial f) \<and>
        (\<forall>y. f y \<noteq> 0 \<longrightarrow> norm y \<le> R)"
    have exponent_lower: "1 < a" and exponent_upper: "a < 2"
      and tau_positive: "0 < tau" and delta_positive: "0 < delta"
      and radius_lower: "delta \<le> R"
      and f_test: "slp_test_function_on UNIV f"
      and f_lp:
        "aim_complex_lp_on_plane (aim_hls_target_exponent a) f"
      and derivative_lp:
        "aim_complex_lp_on_plane a (slp_classical_wirtinger_partial f)"
      and radius_bound: "\<And>y. f y \<noteq> 0 \<Longrightarrow> norm y \<le> R"
      using hypotheses by blast+
    let ?q = "aim_hls_target_exponent a"
    let ?near = "slp_partial_psi_inverse tau 0
      (slp_global_cutoff.slp_near_cutoff_amplitude delta 0 f)"
    let ?far = "slp_partial_psi_inverse tau 0
      (slp_global_far_cutoff_amplitude delta 0 f)"
    let ?B_near = "C_near / ((a - 1) * (2 - a)) *
      ((2 * sqrt pi * delta) * aim_complex_lp_norm ?q f)"
    let ?B_far = "(1 / tau) *
      (4 *
        ((2 / delta) * aim_complex_lp_norm ?q f +
          C_far / ((a - 1) * (2 - a)) *
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
                  aim_complex_lp_norm ?q f))))"
    have near_data:
        "aim_complex_lp_on_plane ?q ?near \<and>
          aim_complex_lp_norm ?q ?near \<le> ?B_near"
      by (rule near_bound[OF exponent_lower exponent_upper delta_positive f_lp])
    have far_data:
        "aim_complex_lp_on_plane ?q ?far \<and>
          aim_complex_lp_norm ?q ?far \<le> ?B_far"
      by (rule far_bound[OF exponent_lower exponent_upper tau_positive
            delta_positive radius_lower f_test f_lp derivative_lp radius_bound])
    have near_lp: "aim_complex_lp_on_plane ?q ?near"
      using near_data by blast
    have near_norm: "aim_complex_lp_norm ?q ?near \<le> ?B_near"
      using near_data by blast
    have far_lp: "aim_complex_lp_on_plane ?q ?far"
      using far_data by blast
    have far_norm: "aim_complex_lp_norm ?q ?far \<le> ?B_far"
      using far_data by blast
    have q_above_two: "2 < ?q"
      by (rule slp_hls_target_exponent_above_two[OF exponent_lower
            exponent_upper])
    have q_one_le: "1 \<le> ?q"
      using q_above_two by linarith
    note sum_data = slp_complex_lp_add_norm_coarse_triangle[
      OF q_one_le near_lp far_lp]
    have split:
        "slp_partial_psi_inverse tau 0 f = (\<lambda>z. ?near z + ?far z)"
      by (rule slp_qstar_smooth_near_far_operator_split[OF delta_positive
            f_test])
    have total_lp:
        "aim_complex_lp_on_plane ?q (slp_partial_psi_inverse tau 0 f)"
      apply (subst split)
      by (rule sum_data(1))
    have component_bound:
        "4 * (aim_complex_lp_norm ?q ?near +
            aim_complex_lp_norm ?q ?far) \<le>
          4 * (?B_near + ?B_far)"
    proof (rule mult_left_mono)
      show "aim_complex_lp_norm ?q ?near + aim_complex_lp_norm ?q ?far
          \<le> ?B_near + ?B_far"
        by (rule add_mono[OF near_norm far_norm])
      show "0 \<le> (4::real)" by simp
    qed
    have total_norm:
        "aim_complex_lp_norm ?q (slp_partial_psi_inverse tau 0 f) \<le>
          4 * (?B_near + ?B_far)"
    proof -
      have "aim_complex_lp_norm ?q (slp_partial_psi_inverse tau 0 f) =
          aim_complex_lp_norm ?q (\<lambda>z. ?near z + ?far z)"
        by (simp only: split)
      also have "... \<le> 4 * (aim_complex_lp_norm ?q ?near +
          aim_complex_lp_norm ?q ?far)"
        by (rule sum_data(2))
      also have "... \<le> 4 * (?B_near + ?B_far)"
        by (rule component_bound)
      finally show ?thesis .
    qed
    show
      "aim_complex_lp_on_plane ?q (slp_partial_psi_inverse tau 0 f) \<and>
        aim_complex_lp_norm ?q (slp_partial_psi_inverse tau 0 f)
          \<le> 4 * (?B_near + ?B_far)"
      using total_lp total_norm by blast
  qed
  show ?thesis
    using C_near_positive C_far_positive all_bound by blast
qed

end

end
