theory Inverse_Schrodinger_Lp_W1p_Smooth_Sobolev_HLS
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_011.Inverse_Schrodinger_Lp_W1p_Zero_Pair_AE_Transport"
begin

section \<open>Compact-smooth planar Sobolev gain from the Cauchy left inverse\<close>

context slp_qstar_centered_smooth_far_hls_context
begin

theorem slp_test_function_planar_sobolev_hls:
  "\<exists>C::real. 0 < C \<and>
    (\<forall>a X f.
      1 < a \<and> a < 2 \<and> slp_test_function_on X f
      \<longrightarrow>
      aim_complex_lp_on_plane (aim_hls_target_exponent a) f \<and>
      aim_complex_lp_norm (aim_hls_target_exponent a) f
        \<le> C / ((a - 1) * (2 - a)) *
          aim_complex_lp_norm a (slp_classical_wirtinger_partial f))"
proof -
  obtain C::real where C_positive: "0 < C"
    and hls:
      "\<And>a g. 1 < a \<Longrightarrow> a < 2 \<Longrightarrow>
        aim_complex_lp_on_plane a g \<Longrightarrow>
        aim_complex_lp_on_plane (aim_hls_target_exponent a)
            (slp_dbar_inverse g) \<and>
        aim_complex_lp_on_plane (aim_hls_target_exponent a)
            (slp_partial_inverse g) \<and>
        aim_complex_lp_norm (aim_hls_target_exponent a)
            (slp_dbar_inverse g)
          \<le> C / ((a - 1) * (2 - a)) * aim_complex_lp_norm a g \<and>
        aim_complex_lp_norm (aim_hls_target_exponent a)
            (slp_partial_inverse g)
          \<le> C / ((a - 1) * (2 - a)) * aim_complex_lp_norm a g"
    using slp_both_cauchy_hls by blast
  show ?thesis
  proof (intro exI[of _ C] conjI)
    show "0 < C"
      by (rule C_positive)
    show "\<forall>a X f.
        1 < a \<and> a < 2 \<and> slp_test_function_on X f
        \<longrightarrow>
        aim_complex_lp_on_plane (aim_hls_target_exponent a) f \<and>
        aim_complex_lp_norm (aim_hls_target_exponent a) f
          \<le> C / ((a - 1) * (2 - a)) *
            aim_complex_lp_norm a (slp_classical_wirtinger_partial f)"
    proof (intro allI impI)
      fix a :: real and X :: "slp_point set" and f :: slp_scalar_field
      assume hypotheses: "1 < a \<and> a < 2 \<and> slp_test_function_on X f"
      from hypotheses have a_lower: "1 < a"
        and a_upper: "a < 2"
        and f_test: "slp_test_function_on X f"
        by blast+
      have a_positive: "0 < a"
        using a_lower by linarith
      have f_test_UNIV: "slp_test_function_on UNIV f"
        using f_test unfolding slp_test_function_on_def by blast
      have derivative_test:
          "slp_test_function_on UNIV (slp_classical_wirtinger_partial f)"
        by (rule slp_classical_wirtinger_partial_test_function[OF f_test_UNIV])
      have derivative_lp:
          "aim_complex_lp_on_plane a (slp_classical_wirtinger_partial f)"
        by (rule slp_test_function_aim_complex_lp_on_plane[
              OF a_positive derivative_test])
      have hls_data:
        "aim_complex_lp_on_plane (aim_hls_target_exponent a)
            (slp_dbar_inverse (slp_classical_wirtinger_partial f)) \<and>
          aim_complex_lp_on_plane (aim_hls_target_exponent a)
            (slp_partial_inverse (slp_classical_wirtinger_partial f)) \<and>
          aim_complex_lp_norm (aim_hls_target_exponent a)
              (slp_dbar_inverse (slp_classical_wirtinger_partial f))
            \<le> C / ((a - 1) * (2 - a)) *
              aim_complex_lp_norm a (slp_classical_wirtinger_partial f) \<and>
          aim_complex_lp_norm (aim_hls_target_exponent a)
              (slp_partial_inverse (slp_classical_wirtinger_partial f))
            \<le> C / ((a - 1) * (2 - a)) *
              aim_complex_lp_norm a (slp_classical_wirtinger_partial f)"
        by (rule hls[OF a_lower a_upper derivative_lp])
      have left_inverse:
        "slp_partial_inverse (slp_classical_wirtinger_partial f) = f"
        by (rule slp_partial_inverse_classical_partial_left_inverse[
              OF f_test_UNIV])
      have f_target_lp:
        "aim_complex_lp_on_plane (aim_hls_target_exponent a) f"
        using hls_data[THEN conjunct2, THEN conjunct1]
        unfolding left_inverse .
      have f_target_bound:
        "aim_complex_lp_norm (aim_hls_target_exponent a) f
          \<le> C / ((a - 1) * (2 - a)) *
            aim_complex_lp_norm a (slp_classical_wirtinger_partial f)"
        using hls_data[THEN conjunct2, THEN conjunct2, THEN conjunct2]
        unfolding left_inverse .
      show "aim_complex_lp_on_plane (aim_hls_target_exponent a) f \<and>
        aim_complex_lp_norm (aim_hls_target_exponent a) f
          \<le> C / ((a - 1) * (2 - a)) *
            aim_complex_lp_norm a (slp_classical_wirtinger_partial f)"
        using f_target_lp f_target_bound by blast
    qed
  qed
qed

end

end
