theory Inverse_Schrodinger_Lp_Qstar_Smooth_Inverse_Sqrt_HLS
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_010.Inverse_Schrodinger_Lp_Partial_Psi_Translation_Covariance"
begin

section \<open>Arbitrary-center inverse-square-root qstar estimate\<close>

context slp_qstar_centered_smooth_far_hls_context
begin

theorem slp_qstar_smooth_inverse_sqrt_hls:
  "\<exists>C::real. 0 < C \<and>
    (\<forall>a tau R c f.
      1 < a \<and> a < 2 \<and> 2 \<le> tau \<and>
      1 \<le> R * sqrt tau \<and>
      slp_test_function_on UNIV f \<and>
      aim_complex_lp_on_plane (aim_hls_target_exponent a) f \<and>
      aim_complex_lp_on_plane a (slp_classical_wirtinger_partial f) \<and>
      (\<forall>y. f y \<noteq> 0 \<longrightarrow> norm (y - c) \<le> R)
      \<longrightarrow>
      aim_complex_lp_on_plane (aim_hls_target_exponent a)
        (slp_partial_psi_inverse tau c f) \<and>
      aim_complex_lp_norm (aim_hls_target_exponent a)
          (slp_partial_psi_inverse tau c f)
        \<le> C / ((a - 1) * (2 - a)) * inverse (sqrt tau) *
          (2 * aim_complex_lp_norm (aim_hls_target_exponent a) f +
            aim_complex_lp_norm a
              (slp_classical_wirtinger_partial f)))"
proof -
  obtain C::real where C_positive: "0 < C"
    and centered:
      "\<And>a tau R f.
        1 < a \<Longrightarrow> a < 2 \<Longrightarrow> 2 \<le> tau \<Longrightarrow>
        1 \<le> R * sqrt tau \<Longrightarrow>
        slp_test_function_on UNIV f \<Longrightarrow>
        aim_complex_lp_on_plane (aim_hls_target_exponent a) f \<Longrightarrow>
        aim_complex_lp_on_plane a
          (slp_classical_wirtinger_partial f) \<Longrightarrow>
        (\<And>y. f y \<noteq> 0 \<Longrightarrow> norm y \<le> R) \<Longrightarrow>
        aim_complex_lp_on_plane (aim_hls_target_exponent a)
          (slp_partial_psi_inverse tau 0 f) \<and>
        aim_complex_lp_norm (aim_hls_target_exponent a)
            (slp_partial_psi_inverse tau 0 f)
          \<le> C / ((a - 1) * (2 - a)) * inverse (sqrt tau) *
            (2 * aim_complex_lp_norm (aim_hls_target_exponent a) f +
              aim_complex_lp_norm a
                (slp_classical_wirtinger_partial f))"
    using slp_qstar_centered_smooth_inverse_sqrt_hls by blast
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
        (\<forall>y. f y \<noteq> 0 \<longrightarrow> norm (y - c) \<le> R)"
    from hypotheses have a_lower: "1 < a"
      and a_upper: "a < 2"
      and tau_lower: "2 \<le> tau"
      and normalized_lower: "1 \<le> R * sqrt tau"
      and f_test: "slp_test_function_on UNIV f"
      and f_membership:
        "aim_complex_lp_on_plane (aim_hls_target_exponent a) f"
      and derivative_membership:
        "aim_complex_lp_on_plane a
          (slp_classical_wirtinger_partial f)"
      and support: "\<And>y. f y \<noteq> 0 \<Longrightarrow> norm (y - c) \<le> R"
      by blast+
    let ?g = "\<lambda>x. f (c + x)"
    have f_smooth: "smooth_on UNIV f"
      using f_test unfolding slp_test_function_on_def by blast
    have g_test: "slp_test_function_on UNIV ?g"
      by (rule slp_test_function_on_UNIV_translate[OF f_test])
    note g_data = slp_aim_complex_lp_on_plane_translate[
      OF f_membership, where c=c]
    have g_membership:
        "aim_complex_lp_on_plane (aim_hls_target_exponent a) ?g"
      by (rule g_data[THEN conjunct1])
    have g_norm:
        "aim_complex_lp_norm (aim_hls_target_exponent a) ?g =
          aim_complex_lp_norm (aim_hls_target_exponent a) f"
      by (rule g_data[THEN conjunct2])
    have derivative_translate:
        "slp_classical_wirtinger_partial ?g =
          (\<lambda>x. slp_classical_wirtinger_partial f (c + x))"
      by (rule ext, rule slp_classical_wirtinger_partial_translate[OF f_smooth])
    note derivative_data = slp_aim_complex_lp_on_plane_translate[
      OF derivative_membership, where c=c]
    have g_derivative_membership:
        "aim_complex_lp_on_plane a
          (slp_classical_wirtinger_partial ?g)"
      using derivative_data[THEN conjunct1]
      by (simp only: derivative_translate)
    have g_derivative_norm:
        "aim_complex_lp_norm a
            (slp_classical_wirtinger_partial ?g) =
          aim_complex_lp_norm a
            (slp_classical_wirtinger_partial f)"
      using derivative_data[THEN conjunct2]
      by (simp only: derivative_translate)
    have g_support: "\<And>y. ?g y \<noteq> 0 \<Longrightarrow> norm y \<le> R"
    proof -
      fix y
      assume "?g y \<noteq> 0"
      then have "norm ((c + y) - c) \<le> R"
        by (rule support)
      then show "norm y \<le> R"
        by simp
    qed
    have centered_data:
        "aim_complex_lp_on_plane (aim_hls_target_exponent a)
            (slp_partial_psi_inverse tau 0 ?g) \<and>
          aim_complex_lp_norm (aim_hls_target_exponent a)
              (slp_partial_psi_inverse tau 0 ?g)
            \<le> C / ((a - 1) * (2 - a)) * inverse (sqrt tau) *
              (2 * aim_complex_lp_norm (aim_hls_target_exponent a) ?g +
                aim_complex_lp_norm a
                  (slp_classical_wirtinger_partial ?g))"
      by (rule centered[OF a_lower a_upper tau_lower normalized_lower
            g_test g_membership g_derivative_membership g_support])
    let ?h = "slp_partial_psi_inverse tau c f"
    let ?k = "slp_partial_psi_inverse tau 0 ?g"
    have output_eq: "?h = (\<lambda>x. ?k (-c + x))"
    proof (rule ext)
      fix x
      have covariance:
          "?h (c + (-c + x)) = ?k (-c + x)"
        by (rule slp_partial_psi_inverse_translate[OF f_test])
      show "?h x = ?k (-c + x)"
        using covariance by simp
    qed
    note output_data = slp_aim_complex_lp_on_plane_translate[
      OF centered_data[THEN conjunct1], where c="-c"]
    have output_membership:
        "aim_complex_lp_on_plane (aim_hls_target_exponent a) ?h"
      using output_data[THEN conjunct1]
      by (simp only: output_eq)
    have output_norm:
        "aim_complex_lp_norm (aim_hls_target_exponent a) ?h =
          aim_complex_lp_norm (aim_hls_target_exponent a) ?k"
      using output_data[THEN conjunct2]
      by (simp only: output_eq)
    have output_bound:
        "aim_complex_lp_norm (aim_hls_target_exponent a) ?k
          \<le> C / ((a - 1) * (2 - a)) * inverse (sqrt tau) *
            (2 * aim_complex_lp_norm (aim_hls_target_exponent a) f +
              aim_complex_lp_norm a
                (slp_classical_wirtinger_partial f))"
      using centered_data[THEN conjunct2]
      by (simp only: g_norm g_derivative_norm)
    show "aim_complex_lp_on_plane (aim_hls_target_exponent a) ?h"
      by (rule output_membership)
    show "aim_complex_lp_norm (aim_hls_target_exponent a) ?h
        \<le> C / ((a - 1) * (2 - a)) * inverse (sqrt tau) *
          (2 * aim_complex_lp_norm (aim_hls_target_exponent a) f +
            aim_complex_lp_norm a
              (slp_classical_wirtinger_partial f))"
      using output_norm output_bound by simp
  qed
qed

end

end
