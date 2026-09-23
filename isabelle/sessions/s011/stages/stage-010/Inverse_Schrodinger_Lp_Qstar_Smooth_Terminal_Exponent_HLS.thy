theory Inverse_Schrodinger_Lp_Qstar_Smooth_Terminal_Exponent_HLS
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_010.Inverse_Schrodinger_Lp_Qstar_Smooth_Both_Orientations_HLS"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Cauchy_Local_Lp_Above_Two"
begin

section \<open>Terminal-exponent specialization of the smooth qstar estimate\<close>

context slp_qstar_centered_smooth_far_hls_context
begin

theorem slp_qstar_smooth_terminal_exponent_inverse_sqrt_hls:
  "\<exists>C::real. 0 < C \<and>
    (\<forall>s tau R c f.
      2 < s \<and> 2 \<le> tau \<and> 1 \<le> R * sqrt tau \<and>
      slp_test_function_on UNIV f \<and>
      aim_complex_lp_on_plane s f \<and>
      aim_complex_lp_on_plane (slp_hls_source_exponent s)
        (slp_classical_wirtinger_partial f) \<and>
      aim_complex_lp_on_plane (slp_hls_source_exponent s)
        (slp_classical_wirtinger_partial (\<lambda>x. cnj (f x))) \<and>
      (\<forall>y. f y \<noteq> 0 \<longrightarrow> norm (y - c) \<le> R)
      \<longrightarrow>
      aim_complex_lp_on_plane s (slp_partial_psi_inverse tau c f) \<and>
      aim_complex_lp_on_plane s (slp_dbar_psi_inverse tau c f) \<and>
      aim_complex_lp_norm s (slp_partial_psi_inverse tau c f)
        \<le> C /
            ((slp_hls_source_exponent s - 1) *
              (2 - slp_hls_source_exponent s)) *
            inverse (sqrt tau) *
          (2 * aim_complex_lp_norm s f +
            aim_complex_lp_norm (slp_hls_source_exponent s)
              (slp_classical_wirtinger_partial f)) \<and>
      aim_complex_lp_norm s (slp_dbar_psi_inverse tau c f)
        \<le> C /
            ((slp_hls_source_exponent s - 1) *
              (2 - slp_hls_source_exponent s)) *
            inverse (sqrt tau) *
          (2 * aim_complex_lp_norm s f +
            aim_complex_lp_norm (slp_hls_source_exponent s)
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
        aim_complex_lp_on_plane a
          (slp_classical_wirtinger_partial (\<lambda>x. cnj (f x))) \<Longrightarrow>
        (\<And>y. f y \<noteq> 0 \<Longrightarrow> norm (y - c) \<le> R) \<Longrightarrow>
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
                (slp_classical_wirtinger_partial (\<lambda>x. cnj (f x))))"
    using slp_qstar_smooth_both_orientations_inverse_sqrt_hls by blast
  show ?thesis
  proof (intro exI[of _ C] conjI allI impI)
    show "0 < C"
      by (rule C_positive)
    fix s tau R c f
    assume hypotheses:
      "2 < s \<and> 2 \<le> tau \<and> 1 \<le> R * sqrt tau \<and>
        slp_test_function_on UNIV f \<and>
        aim_complex_lp_on_plane s f \<and>
        aim_complex_lp_on_plane (slp_hls_source_exponent s)
          (slp_classical_wirtinger_partial f) \<and>
        aim_complex_lp_on_plane (slp_hls_source_exponent s)
          (slp_classical_wirtinger_partial (\<lambda>x. cnj (f x))) \<and>
        (\<forall>y. f y \<noteq> 0 \<longrightarrow> norm (y - c) \<le> R)"
    from hypotheses have s_lower: "2 < s"
      and tau_lower: "2 \<le> tau"
      and normalized_lower: "1 \<le> R * sqrt tau"
      and f_test: "slp_test_function_on UNIV f"
      and f_membership: "aim_complex_lp_on_plane s f"
      and f_derivative_membership:
        "aim_complex_lp_on_plane (slp_hls_source_exponent s)
          (slp_classical_wirtinger_partial f)"
      and conjugate_derivative_membership:
        "aim_complex_lp_on_plane (slp_hls_source_exponent s)
          (slp_classical_wirtinger_partial (\<lambda>x. cnj (f x)))"
      and support: "\<And>y. f y \<noteq> 0 \<Longrightarrow> norm (y - c) \<le> R"
      by blast+
    have source_lower: "1 < slp_hls_source_exponent s"
      and source_upper: "slp_hls_source_exponent s < 2"
      using slp_hls_source_exponent_bounds[OF s_lower] by auto
    have target_identity:
        "aim_hls_target_exponent (slp_hls_source_exponent s) = s"
      by (rule slp_hls_source_target_identity[OF s_lower])
    have f_target_membership:
        "aim_complex_lp_on_plane
          (aim_hls_target_exponent (slp_hls_source_exponent s)) f"
      using f_membership by (simp only: target_identity)
    have specialized:
        "aim_complex_lp_on_plane
            (aim_hls_target_exponent (slp_hls_source_exponent s))
            (slp_partial_psi_inverse tau c f) \<and>
          aim_complex_lp_on_plane
            (aim_hls_target_exponent (slp_hls_source_exponent s))
            (slp_dbar_psi_inverse tau c f) \<and>
          aim_complex_lp_norm
              (aim_hls_target_exponent (slp_hls_source_exponent s))
              (slp_partial_psi_inverse tau c f)
            \<le> C /
                ((slp_hls_source_exponent s - 1) *
                  (2 - slp_hls_source_exponent s)) *
                inverse (sqrt tau) *
              (2 * aim_complex_lp_norm
                  (aim_hls_target_exponent (slp_hls_source_exponent s)) f +
                aim_complex_lp_norm (slp_hls_source_exponent s)
                  (slp_classical_wirtinger_partial f)) \<and>
          aim_complex_lp_norm
              (aim_hls_target_exponent (slp_hls_source_exponent s))
              (slp_dbar_psi_inverse tau c f)
            \<le> C /
                ((slp_hls_source_exponent s - 1) *
                  (2 - slp_hls_source_exponent s)) *
                inverse (sqrt tau) *
              (2 * aim_complex_lp_norm
                  (aim_hls_target_exponent (slp_hls_source_exponent s)) f +
                aim_complex_lp_norm (slp_hls_source_exponent s)
                  (slp_classical_wirtinger_partial (\<lambda>x. cnj (f x))))"
      by (rule qstar[OF source_lower source_upper tau_lower normalized_lower
            f_test f_target_membership f_derivative_membership
            conjugate_derivative_membership support])
    show "aim_complex_lp_on_plane s (slp_partial_psi_inverse tau c f)"
      using specialized[THEN conjunct1]
      by (simp only: target_identity)
    show "aim_complex_lp_on_plane s (slp_dbar_psi_inverse tau c f)"
      using specialized[THEN conjunct2, THEN conjunct1]
      by (simp only: target_identity)
    show "aim_complex_lp_norm s (slp_partial_psi_inverse tau c f)
        \<le> C /
            ((slp_hls_source_exponent s - 1) *
              (2 - slp_hls_source_exponent s)) *
            inverse (sqrt tau) *
          (2 * aim_complex_lp_norm s f +
            aim_complex_lp_norm (slp_hls_source_exponent s)
              (slp_classical_wirtinger_partial f))"
      using specialized[THEN conjunct2, THEN conjunct2, THEN conjunct1]
      by (simp only: target_identity)
    show "aim_complex_lp_norm s (slp_dbar_psi_inverse tau c f)
        \<le> C /
            ((slp_hls_source_exponent s - 1) *
              (2 - slp_hls_source_exponent s)) *
            inverse (sqrt tau) *
          (2 * aim_complex_lp_norm s f +
            aim_complex_lp_norm (slp_hls_source_exponent s)
              (slp_classical_wirtinger_partial (\<lambda>x. cnj (f x))))"
      using specialized[THEN conjunct2, THEN conjunct2, THEN conjunct2]
      by (simp only: target_identity)
  qed
qed

end

end
