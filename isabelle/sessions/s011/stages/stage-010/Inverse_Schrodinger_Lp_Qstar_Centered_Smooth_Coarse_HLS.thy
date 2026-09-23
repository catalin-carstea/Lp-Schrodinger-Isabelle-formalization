theory Inverse_Schrodinger_Lp_Qstar_Centered_Smooth_Coarse_HLS
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_010.Inverse_Schrodinger_Lp_Qstar_Centered_Smooth_Total_HLS"
    "HOL-Decision_Procs.Commutative_Ring"
begin

section \<open>Coarse centered smooth scale estimate\<close>

lemma slp_qstar_smooth_raw_scale_identity:
  fixes cn cf u s d n v w l A m j :: real
  shows
    "4 *
        (cn * u * ((2 * s * d) * n) +
          v *
            (4 *
              ((2 * w) * n +
                cf * u *
                  (4 *
                    (4 *
                      ((2 * w) * m + (l * w) * (A * n)) +
                      w * j * n))))) =
      (8 * s * cn) * u * (d * n) +
        (v * w) *
          (32 * n +
            ((256 * cf * l * A + 64 * cf * j) * u) * n +
            (512 * cf * u) * m)"
  by (simp add: algebra_simps mult_ac)

lemma slp_qstar_smooth_f_coefficient_identity:
  fixes cf l A j u n :: real
  shows
    "(32 * u) * n +
        ((256 * cf * l * A + 64 * cf * j) * u) * n =
      ((32 + 256 * cf * l * A + 64 * cf * j) * u) * n"
  by (simp add: algebra_simps mult_ac)

lemma slp_qstar_smooth_coarse_distributivity:
  fixes C u d n v w m :: real
  shows
    "C * u * (d * n) + (v * w) * (C * u * (n + m)) =
      C * u * (d * n + (v * w) * (n + m))"
  by (simp add: algebra_simps mult_ac)

context slp_qstar_centered_smooth_far_hls_context
begin

theorem slp_qstar_centered_smooth_coarse_hls:
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
        (slp_partial_psi_inverse tau 0 f) \<and>
      aim_complex_lp_norm (aim_hls_target_exponent a)
          (slp_partial_psi_inverse tau 0 f)
        \<le> C / ((a - 1) * (2 - a)) *
          (delta * aim_complex_lp_norm (aim_hls_target_exponent a) f +
            (1 / (tau * delta)) *
              (aim_complex_lp_norm (aim_hls_target_exponent a) f +
                aim_complex_lp_norm a
                  (slp_classical_wirtinger_partial f))))"
proof -
  obtain C_near C_far::real where C_near_positive: "0 < C_near"
    and C_far_positive: "0 < C_far"
    and total_bound:
      "\<And>a tau delta R f.
        1 < a \<Longrightarrow> a < 2 \<Longrightarrow> 0 < tau \<Longrightarrow>
        0 < delta \<Longrightarrow> delta \<le> R \<Longrightarrow>
        slp_test_function_on UNIV f \<Longrightarrow>
        aim_complex_lp_on_plane (aim_hls_target_exponent a) f \<Longrightarrow>
        aim_complex_lp_on_plane a
          (slp_classical_wirtinger_partial f) \<Longrightarrow>
        (\<And>y. f y \<noteq> 0 \<Longrightarrow> norm y \<le> R) \<Longrightarrow>
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
    using slp_qstar_centered_smooth_total_hls by blast
  let ?A = "(integral\<^sup>L lborel
      (slp_squared_radial_annulus 1 2)) powr (1 / 2)"
  let ?J = "slp_qstar_annular_J2_unit_coefficient_mass powr (1 / 2)"
  let ?K_near = "8 * sqrt pi * C_near"
  let ?K_f = "32 + 256 * C_far * slp_global_cutoff_L * ?A +
    64 * C_far * ?J"
  let ?K_d = "512 * C_far"
  let ?C = "1 + ?K_near + ?K_f + ?K_d"
  have A_nonnegative: "0 \<le> ?A" by simp
  have J_nonnegative: "0 \<le> ?J" by simp
  have cutoff_nonnegative: "0 \<le> slp_global_cutoff_L"
    by (rule slp_global_cutoff_profile_spec[THEN conjunct2,
          THEN conjunct2, THEN conjunct1])
  have C_near_nonnegative: "0 \<le> C_near"
    using C_near_positive by linarith
  have C_far_nonnegative: "0 \<le> C_far"
    using C_far_positive by linarith
  have sqrt_pi_nonnegative: "0 \<le> sqrt pi" by simp
  have K_near_nonnegative: "0 \<le> ?K_near"
    by (rule mult_nonneg_nonneg[OF mult_nonneg_nonneg[OF _ sqrt_pi_nonnegative]
          C_near_nonnegative]) simp
  have cutoff_coefficient_nonnegative:
      "0 \<le> 256 * C_far * slp_global_cutoff_L * ?A"
    by (rule mult_nonneg_nonneg[OF mult_nonneg_nonneg[OF mult_nonneg_nonneg[OF _
          C_far_nonnegative] cutoff_nonnegative] A_nonnegative]) simp
  have J_coefficient_nonnegative: "0 \<le> 64 * C_far * ?J"
    by (rule mult_nonneg_nonneg[OF mult_nonneg_nonneg[OF _ C_far_nonnegative]
          J_nonnegative]) simp
  have K_f_nonnegative: "0 \<le> ?K_f"
    using cutoff_coefficient_nonnegative J_coefficient_nonnegative by linarith
  have K_d_nonnegative: "0 \<le> ?K_d"
    by (rule mult_nonneg_nonneg[OF _ C_far_nonnegative]) simp
  have C_positive: "0 < ?C"
    using K_near_nonnegative K_f_nonnegative K_d_nonnegative by linarith
  show ?thesis
  proof (intro exI[of _ ?C] conjI allI impI)
    show "0 < ?C" by (rule C_positive)
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
      and f_lp: "aim_complex_lp_on_plane (aim_hls_target_exponent a) f"
      and derivative_lp:
        "aim_complex_lp_on_plane a (slp_classical_wirtinger_partial f)"
      and radius_bound: "\<And>y. f y \<noteq> 0 \<Longrightarrow> norm y \<le> R"
      using hypotheses by blast+
    let ?q = "aim_hls_target_exponent a"
    let ?D = "(a - 1) * (2 - a)"
    let ?N = "aim_complex_lp_norm ?q f"
    let ?M = "aim_complex_lp_norm a
      (slp_classical_wirtinger_partial f)"
    have total_data:
        "aim_complex_lp_on_plane ?q (slp_partial_psi_inverse tau 0 f) \<and>
          aim_complex_lp_norm ?q (slp_partial_psi_inverse tau 0 f)
            \<le> 4 *
              (C_near / ?D * ((2 * sqrt pi * delta) * ?N) +
                (1 / tau) *
                  (4 *
                    ((2 / delta) * ?N +
                      C_far / ?D *
                        (4 *
                          (4 *
                            ((2 / delta) * ?M +
                              (slp_global_cutoff_L / delta) * (?A * ?N)) +
                            (1 / delta) * ?J * ?N)))))"
      by (rule total_bound[OF exponent_lower exponent_upper tau_positive
            delta_positive radius_lower f_test f_lp derivative_lp
            radius_bound])
    have total_membership:
        "aim_complex_lp_on_plane ?q (slp_partial_psi_inverse tau 0 f)"
      using total_data by (rule conjunct1)
    have total_norm_raw:
        "aim_complex_lp_norm ?q (slp_partial_psi_inverse tau 0 f)
          \<le> 4 *
            (C_near / ?D * ((2 * sqrt pi * delta) * ?N) +
              (1 / tau) *
                (4 *
                  ((2 / delta) * ?N +
                    C_far / ?D *
                      (4 *
                        (4 *
                          ((2 / delta) * ?M +
                            (slp_global_cutoff_L / delta) * (?A * ?N)) +
                          (1 / delta) * ?J * ?N)))))"
      using total_data by (rule conjunct2)
    have D_positive: "0 < ?D"
    proof (rule mult_pos_pos)
      show "0 < a - 1" using exponent_lower by linarith
      show "0 < 2 - a" using exponent_upper by linarith
    qed
    have D_le_one: "?D \<le> 1"
    proof -
      have "(a - 1) * (2 - a) \<le> (1::real) * 1"
      proof (rule mult_mono)
        show "a - 1 \<le> 1" using exponent_upper by linarith
        show "2 - a \<le> 1" using exponent_lower by linarith
        show "0 \<le> (1::real)" by simp
        show "0 \<le> 2 - a" using exponent_upper by linarith
      qed
      then show ?thesis by simp
    qed
    have N_nonnegative: "0 \<le> ?N"
      unfolding aim_complex_lp_norm_def by simp
    have M_nonnegative: "0 \<le> ?M"
      unfolding aim_complex_lp_norm_def by simp
    have K_near_le_C: "?K_near \<le> ?C"
      using K_f_nonnegative K_d_nonnegative by linarith
    have K_f_le_C: "?K_f \<le> ?C"
      using K_near_nonnegative K_d_nonnegative by linarith
    have K_d_le_C: "?K_d \<le> ?C"
      using K_near_nonnegative K_f_nonnegative by linarith
    have raw_identity:
        "4 *
            (C_near / ?D * ((2 * sqrt pi * delta) * ?N) +
              (1 / tau) *
                (4 *
                  ((2 / delta) * ?N +
                    C_far / ?D *
                      (4 *
                        (4 *
                          ((2 / delta) * ?M +
                            (slp_global_cutoff_L / delta) * (?A * ?N)) +
                          (1 / delta) * ?J * ?N))))) =
          ?K_near / ?D * (delta * ?N) +
            (1 / (tau * delta)) *
              (32 * ?N +
                ((256 * C_far * slp_global_cutoff_L * ?A +
                    64 * C_far * ?J) / ?D) * ?N +
                (?K_d / ?D) * ?M)"
    proof -
      note identity = slp_qstar_smooth_raw_scale_identity[
        where cn = C_near and cf = C_far and u = "inverse ?D"
          and s = "sqrt pi" and d = delta and n = ?N
          and v = "inverse tau" and w = "inverse delta"
          and l = slp_global_cutoff_L and A = ?A and m = ?M and j = ?J]
      show ?thesis
        using identity by (simp only: divide_inverse inverse_mult_distrib
          mult.left_neutral)
    qed
    have one_le_inverse_D: "1 \<le> 1 / ?D"
      using one_le_inverse[OF D_positive D_le_one]
      by (simp only: divide_inverse mult.left_neutral)
    have plain_f_bound: "32 * ?N \<le> (32 / ?D) * ?N"
    proof (rule mult_right_mono)
      show "32 \<le> 32 / ?D"
        using one_le_inverse_D by (simp add: divide_inverse)
      show "0 \<le> ?N" by (rule N_nonnegative)
    qed
    have f_coefficient_bound:
        "32 * ?N +
            ((256 * C_far * slp_global_cutoff_L * ?A +
                64 * C_far * ?J) / ?D) * ?N
          \<le> (?K_f / ?D) * ?N"
    proof -
      have "32 * ?N +
            ((256 * C_far * slp_global_cutoff_L * ?A +
                64 * C_far * ?J) / ?D) * ?N
          \<le> (32 / ?D) * ?N +
            ((256 * C_far * slp_global_cutoff_L * ?A +
                64 * C_far * ?J) / ?D) * ?N"
        by (rule add_right_mono[OF plain_f_bound])
      also have "... = (?K_f / ?D) * ?N"
      proof -
        note identity = slp_qstar_smooth_f_coefficient_identity[
          where cf = C_far and l = slp_global_cutoff_L and A = ?A
            and j = ?J and u = "inverse ?D" and n = ?N]
        show ?thesis using identity by (simp only: divide_inverse
          mult.left_neutral)
      qed
      finally show ?thesis .
    qed
    have f_bound: "(?K_f / ?D) * ?N \<le> (?C / ?D) * ?N"
    proof (rule mult_right_mono)
      show "?K_f / ?D \<le> ?C / ?D"
        using K_f_le_C D_positive by (simp add: divide_right_mono)
      show "0 \<le> ?N" by (rule N_nonnegative)
    qed
    have derivative_bound:
        "(?K_d / ?D) * ?M \<le> (?C / ?D) * ?M"
    proof (rule mult_right_mono)
      show "?K_d / ?D \<le> ?C / ?D"
        using K_d_le_C D_positive by (simp add: divide_right_mono)
      show "0 \<le> ?M" by (rule M_nonnegative)
    qed
    have far_inner_bound:
        "32 * ?N +
            ((256 * C_far * slp_global_cutoff_L * ?A +
                64 * C_far * ?J) / ?D) * ?N +
            (?K_d / ?D) * ?M
          \<le> (?C / ?D) * (?N + ?M)"
    proof -
      have "32 * ?N +
            ((256 * C_far * slp_global_cutoff_L * ?A +
                64 * C_far * ?J) / ?D) * ?N +
            (?K_d / ?D) * ?M
          \<le> (?K_f / ?D) * ?N + (?K_d / ?D) * ?M"
        by (rule add_mono[OF f_coefficient_bound order_refl])
      also have "... \<le> (?C / ?D) * ?N + (?C / ?D) * ?M"
        by (rule add_mono[OF f_bound derivative_bound])
      also have "... = (?C / ?D) * (?N + ?M)"
        by (rule distrib_left[symmetric])
      finally show ?thesis .
    qed
    have scale_nonnegative: "0 \<le> 1 / (tau * delta)"
    proof -
      have "0 < tau * delta"
        by (rule mult_pos_pos[OF tau_positive delta_positive])
      then show ?thesis by simp
    qed
    have far_bound_coarse:
        "(1 / (tau * delta)) *
            (32 * ?N +
              ((256 * C_far * slp_global_cutoff_L * ?A +
                  64 * C_far * ?J) / ?D) * ?N +
              (?K_d / ?D) * ?M)
          \<le> (1 / (tau * delta)) *
            ((?C / ?D) * (?N + ?M))"
      by (rule mult_left_mono[OF far_inner_bound scale_nonnegative])
    have near_bound_coarse:
        "?K_near / ?D * (delta * ?N) \<le>
          ?C / ?D * (delta * ?N)"
    proof (rule mult_right_mono)
      show "?K_near / ?D \<le> ?C / ?D"
        using K_near_le_C D_positive by (simp add: divide_right_mono)
      show "0 \<le> delta * ?N"
        by (rule mult_nonneg_nonneg)
          (use delta_positive N_nonnegative in linarith)+
    qed
    have norm_bound:
        "aim_complex_lp_norm ?q (slp_partial_psi_inverse tau 0 f)
          \<le> ?C / ?D *
            (delta * ?N + (1 / (tau * delta)) * (?N + ?M))"
    proof -
      have "aim_complex_lp_norm ?q (slp_partial_psi_inverse tau 0 f)
          \<le> ?K_near / ?D * (delta * ?N) +
            (1 / (tau * delta)) *
              (32 * ?N +
                ((256 * C_far * slp_global_cutoff_L * ?A +
                    64 * C_far * ?J) / ?D) * ?N +
                (?K_d / ?D) * ?M)"
        using total_norm_raw by (simp only: raw_identity)
      also have "... \<le> ?C / ?D * (delta * ?N) +
          (1 / (tau * delta)) * ((?C / ?D) * (?N + ?M))"
        by (rule add_mono[OF near_bound_coarse far_bound_coarse])
      also have "... = ?C / ?D *
          (delta * ?N + (1 / (tau * delta)) * (?N + ?M))"
      proof -
        note identity = slp_qstar_smooth_coarse_distributivity[
          where C = ?C and u = "inverse ?D" and d = delta and n = ?N
            and v = "inverse tau" and w = "inverse delta" and m = ?M]
        show ?thesis
          using identity by (simp only: divide_inverse inverse_mult_distrib
            mult.left_neutral)
      qed
      finally show ?thesis .
    qed
    show "aim_complex_lp_on_plane ?q (slp_partial_psi_inverse tau 0 f)"
      by (rule total_membership)
    show "aim_complex_lp_norm ?q (slp_partial_psi_inverse tau 0 f)
        \<le> ?C / ?D *
          (delta * ?N + (1 / (tau * delta)) * (?N + ?M))"
      by (rule norm_bound)
  qed
qed

end

end
