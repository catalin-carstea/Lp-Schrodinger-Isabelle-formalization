theory Inverse_Schrodinger_Lp_Qstar_Smooth_Both_Orientations_HLS
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_010.Inverse_Schrodinger_Lp_Qstar_Smooth_Inverse_Sqrt_HLS"
begin

section \<open>Both Cauchy orientations for the smooth qstar estimate\<close>

context slp_qstar_centered_smooth_far_hls_context
begin

theorem slp_qstar_smooth_both_orientations_inverse_sqrt_hls:
  "\<exists>C::real. 0 < C \<and>
    (\<forall>a tau R c f.
      1 < a \<and> a < 2 \<and> 2 \<le> tau \<and>
      1 \<le> R * sqrt tau \<and>
      slp_test_function_on UNIV f \<and>
      aim_complex_lp_on_plane (aim_hls_target_exponent a) f \<and>
      aim_complex_lp_on_plane a (slp_classical_wirtinger_partial f) \<and>
      aim_complex_lp_on_plane a
        (slp_classical_wirtinger_partial (\<lambda>x. cnj (f x))) \<and>
      (\<forall>y. f y \<noteq> 0 \<longrightarrow> norm (y - c) \<le> R)
      \<longrightarrow>
      aim_complex_lp_on_plane (aim_hls_target_exponent a)
        (slp_partial_psi_inverse tau c f) \<and>
      aim_complex_lp_on_plane (aim_hls_target_exponent a)
        (slp_dbar_psi_inverse tau c f) \<and>
      aim_complex_lp_norm (aim_hls_target_exponent a)
          (slp_partial_psi_inverse tau c f)
        \<le> C / ((a - 1) * (2 - a)) * inverse (sqrt tau) *
          (2 * aim_complex_lp_norm (aim_hls_target_exponent a) f +
            aim_complex_lp_norm a
              (slp_classical_wirtinger_partial f)) \<and>
      aim_complex_lp_norm (aim_hls_target_exponent a)
          (slp_dbar_psi_inverse tau c f)
        \<le> C / ((a - 1) * (2 - a)) * inverse (sqrt tau) *
          (2 * aim_complex_lp_norm (aim_hls_target_exponent a) f +
            aim_complex_lp_norm a
              (slp_classical_wirtinger_partial (\<lambda>x. cnj (f x)))))"
proof -
  obtain C::real where C_positive: "0 < C"
    and qstar:
      "\<And>a tau R c f.
        1 < a \<Longrightarrow> a < 2 \<Longrightarrow> 2 \<le> tau \<Longrightarrow>
        1 \<le> R * sqrt tau \<Longrightarrow>
        slp_test_function_on UNIV f \<Longrightarrow>
        aim_complex_lp_on_plane (aim_hls_target_exponent a) f \<Longrightarrow>
        aim_complex_lp_on_plane a
          (slp_classical_wirtinger_partial f) \<Longrightarrow>
        (\<And>y. f y \<noteq> 0 \<Longrightarrow> norm (y - c) \<le> R) \<Longrightarrow>
        aim_complex_lp_on_plane (aim_hls_target_exponent a)
          (slp_partial_psi_inverse tau c f) \<and>
        aim_complex_lp_norm (aim_hls_target_exponent a)
            (slp_partial_psi_inverse tau c f)
          \<le> C / ((a - 1) * (2 - a)) * inverse (sqrt tau) *
            (2 * aim_complex_lp_norm (aim_hls_target_exponent a) f +
              aim_complex_lp_norm a
                (slp_classical_wirtinger_partial f))"
    using slp_qstar_smooth_inverse_sqrt_hls by blast
  show ?thesis
  proof (intro exI[of _ C] conjI allI impI)
    show "0 < C"
      by (rule C_positive)
    fix a tau R c f
    assume hypotheses:
      "1 < a \<and> a < 2 \<and> 2 \<le> tau \<and>
        1 \<le> R * sqrt tau \<and>
        slp_test_function_on UNIV f \<and>
        aim_complex_lp_on_plane (aim_hls_target_exponent a) f \<and>
        aim_complex_lp_on_plane a (slp_classical_wirtinger_partial f) \<and>
        aim_complex_lp_on_plane a
          (slp_classical_wirtinger_partial (\<lambda>x. cnj (f x))) \<and>
        (\<forall>y. f y \<noteq> 0 \<longrightarrow> norm (y - c) \<le> R)"
    from hypotheses have a_lower: "1 < a"
      and a_upper: "a < 2"
      and tau_lower: "2 \<le> tau"
      and normalized_lower: "1 \<le> R * sqrt tau"
      and f_test: "slp_test_function_on UNIV f"
      and f_membership:
        "aim_complex_lp_on_plane (aim_hls_target_exponent a) f"
      and f_derivative_membership:
        "aim_complex_lp_on_plane a (slp_classical_wirtinger_partial f)"
      and conjugate_derivative_membership:
        "aim_complex_lp_on_plane a
          (slp_classical_wirtinger_partial (\<lambda>x. cnj (f x)))"
      and support: "\<And>y. f y \<noteq> 0 \<Longrightarrow> norm (y - c) \<le> R"
      by blast+
    have partial_data:
        "aim_complex_lp_on_plane (aim_hls_target_exponent a)
            (slp_partial_psi_inverse tau c f) \<and>
          aim_complex_lp_norm (aim_hls_target_exponent a)
              (slp_partial_psi_inverse tau c f)
            \<le> C / ((a - 1) * (2 - a)) * inverse (sqrt tau) *
              (2 * aim_complex_lp_norm (aim_hls_target_exponent a) f +
                aim_complex_lp_norm a
                  (slp_classical_wirtinger_partial f))"
      by (rule qstar[OF a_lower a_upper tau_lower normalized_lower
            f_test f_membership f_derivative_membership support])
    let ?g = "\<lambda>x. cnj (f x)"
    have g_test: "slp_test_function_on UNIV ?g"
      using f_test by simp
    have g_membership:
        "aim_complex_lp_on_plane (aim_hls_target_exponent a) ?g"
      using f_membership by simp
    have g_support: "\<And>y. ?g y \<noteq> 0 \<Longrightarrow> norm (y - c) \<le> R"
    proof -
      fix y
      assume "?g y \<noteq> 0"
      then have "f y \<noteq> 0"
        by simp
      then show "norm (y - c) \<le> R"
        by (rule support)
    qed
    have conjugated_data:
        "aim_complex_lp_on_plane (aim_hls_target_exponent a)
            (slp_partial_psi_inverse tau c ?g) \<and>
          aim_complex_lp_norm (aim_hls_target_exponent a)
              (slp_partial_psi_inverse tau c ?g)
            \<le> C / ((a - 1) * (2 - a)) * inverse (sqrt tau) *
              (2 * aim_complex_lp_norm (aim_hls_target_exponent a) ?g +
                aim_complex_lp_norm a
                  (slp_classical_wirtinger_partial ?g))"
      by (rule qstar[OF a_lower a_upper tau_lower normalized_lower
            g_test g_membership conjugate_derivative_membership g_support])
    have output_conjugate:
        "slp_partial_psi_inverse tau c ?g =
          (\<lambda>x. cnj (slp_dbar_psi_inverse tau c f x))"
      by (rule ext) simp
    have dbar_membership:
        "aim_complex_lp_on_plane (aim_hls_target_exponent a)
          (slp_dbar_psi_inverse tau c f)"
      using conjugated_data[THEN conjunct1]
      by (simp only: output_conjugate aim_complex_lp_on_plane_cnj_iff)
    have dbar_bound:
        "aim_complex_lp_norm (aim_hls_target_exponent a)
            (slp_dbar_psi_inverse tau c f)
          \<le> C / ((a - 1) * (2 - a)) * inverse (sqrt tau) *
            (2 * aim_complex_lp_norm (aim_hls_target_exponent a) f +
              aim_complex_lp_norm a
                (slp_classical_wirtinger_partial ?g))"
      using conjugated_data[THEN conjunct2]
      by (simp only: output_conjugate aim_complex_lp_norm_cnj)
    show "aim_complex_lp_on_plane (aim_hls_target_exponent a)
        (slp_partial_psi_inverse tau c f)"
      by (rule partial_data[THEN conjunct1])
    show "aim_complex_lp_on_plane (aim_hls_target_exponent a)
        (slp_dbar_psi_inverse tau c f)"
      by (rule dbar_membership)
    show "aim_complex_lp_norm (aim_hls_target_exponent a)
          (slp_partial_psi_inverse tau c f)
        \<le> C / ((a - 1) * (2 - a)) * inverse (sqrt tau) *
          (2 * aim_complex_lp_norm (aim_hls_target_exponent a) f +
            aim_complex_lp_norm a
              (slp_classical_wirtinger_partial f))"
      by (rule partial_data[THEN conjunct2])
    show "aim_complex_lp_norm (aim_hls_target_exponent a)
          (slp_dbar_psi_inverse tau c f)
        \<le> C / ((a - 1) * (2 - a)) * inverse (sqrt tau) *
          (2 * aim_complex_lp_norm (aim_hls_target_exponent a) f +
            aim_complex_lp_norm a
              (slp_classical_wirtinger_partial (\<lambda>x. cnj (f x))))"
      by (rule dbar_bound)
  qed
qed

end

end
