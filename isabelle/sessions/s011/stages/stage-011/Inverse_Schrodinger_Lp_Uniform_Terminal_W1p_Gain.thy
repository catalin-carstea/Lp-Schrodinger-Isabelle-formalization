theory Inverse_Schrodinger_Lp_Uniform_Terminal_W1p_Gain
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_011.Inverse_Schrodinger_Lp_Test_W1p_Membership"
begin

section \<open>The supported test norm is the whole-plane norm\<close>

lemma slp_test_function_w1p_norm_on_plane:
  assumes f_test: "slp_test_function_on X f"
  shows "slp_w1p_norm_on p X f (slp_classical_gradient f) =
    slp_w1p_norm_on p UNIV f (slp_classical_gradient f)"
proof -
  have f_restriction: "slp_restrict_field X f = f"
    by (rule slp_test_function_restrict_field_eq[OF f_test])
  have gradient_component:
      "(\<lambda>x. slp_classical_gradient f x $ i) = slp_complex_partial_derivative f i"
    for i :: 2
    by (rule ext) (simp add: slp_classical_gradient_def)
  have derivative_restriction:
      "slp_restrict_field X (slp_complex_partial_derivative f i) =
        slp_complex_partial_derivative f i"
    for i :: 2
    by (rule slp_test_function_partial_restrict_field_eq[OF f_test])
  have plane_restriction: "slp_restrict_field UNIV h = h"
    for h :: slp_scalar_field
    by (rule ext) (simp add: slp_restrict_field_def)
  show ?thesis
    unfolding slp_w1p_norm_on_def
    by (simp only: gradient_component f_restriction
          derivative_restriction plane_restriction)
qed

section \<open>A uniform whole-plane terminal Sobolev gain\<close>

context slp_qstar_centered_smooth_far_hls_context
begin

theorem slp_uniform_terminal_w1p_gain_plane:
  assumes s_lower: "2 < s" and K_bounded: "bounded K"
  shows "\<exists>C::real. 0 < C \<and>
    (\<forall>tau c f epsilon orientation.
      2 \<le> tau \<and> slp_test_function_on K f \<and> epsilon \<in> {-1, 1}
      \<longrightarrow>
      aim_complex_lp_on_plane s
        (slp_cauchy_transform orientation
          (slp_oscillatory_modulation (epsilon * tau) c f)) \<and>
      aim_complex_lp_norm s
        (slp_cauchy_transform orientation
          (slp_oscillatory_modulation (epsilon * tau) c f))
        \<le> C * inverse (sqrt tau) *
          slp_w1p_norm_on (slp_hls_source_exponent s) UNIV f (slp_classical_gradient f))"
proof -
  let ?a = "slp_hls_source_exponent s"
  have a_lower: "1 < ?a"
    by (rule slp_hls_source_exponent_bounds(1)[OF s_lower])
  have a_upper: "?a < 2"
    by (rule slp_hls_source_exponent_bounds(2)[OF s_lower])
  have a_positive: "0 < ?a" using a_lower by linarith
  have target_identity: "aim_hls_target_exponent ?a = s"
    by (rule slp_hls_source_target_identity[OF s_lower])
  obtain C::real where C_positive: "0 < C"
    and rough_gain:
      "\<And>tau c f Df epsilon orientation.
        2 \<le> tau \<Longrightarrow> slp_w1p_zero_pair_on ?a K f Df \<Longrightarrow>
        epsilon \<in> {-1, 1} \<Longrightarrow>
        aim_complex_lp_on_plane (aim_hls_target_exponent ?a)
          (slp_cauchy_transform orientation
            (slp_oscillatory_modulation (epsilon * tau) c (slp_restrict_field K f))) \<and>
        aim_complex_lp_norm (aim_hls_target_exponent ?a)
          (slp_cauchy_transform orientation
            (slp_oscillatory_modulation (epsilon * tau) c (slp_restrict_field K f)))
          \<le> C * inverse (sqrt tau) * slp_w1p_norm_on ?a K f Df"
    using slp_w1p_zero_pair_all_orientation_gain[OF a_lower a_upper K_bounded]
    by blast
  have smooth_gain:
      "aim_complex_lp_on_plane s
          (slp_cauchy_transform orientation
            (slp_oscillatory_modulation (epsilon * tau) c f)) \<and>
        aim_complex_lp_norm s
          (slp_cauchy_transform orientation
            (slp_oscillatory_modulation (epsilon * tau) c f))
          \<le> C * inverse (sqrt tau) *
            slp_w1p_norm_on ?a UNIV f (slp_classical_gradient f)"
    if tau_lower: "2 \<le> tau" and f_test: "slp_test_function_on K f"
      and epsilon_sign: "epsilon \<in> {-1, 1}"
    for tau :: real and c :: slp_point and f :: slp_scalar_field
      and epsilon :: real and orientation :: slp_cauchy_orientation
  proof -
    have f_zero_pair: "slp_w1p_zero_pair_on ?a K f (slp_classical_gradient f)"
      by (rule slp_test_function_w1p_zero_pair[OF a_positive f_test])
    note application = rough_gain[OF tau_lower f_zero_pair epsilon_sign]
    show ?thesis
      using application
      by (simp only: target_identity slp_test_function_restrict_field_eq[OF f_test]
            slp_test_function_w1p_norm_on_plane[OF f_test])
  qed
  show ?thesis
    by (rule exI[of _ C], rule conjI[OF C_positive])
      (use smooth_gain in blast)
qed

section \<open>The terminal estimate on every Borel target set\<close>

theorem slp_uniform_terminal_w1p_gain_local:
  assumes s_lower: "2 < s" and K_compact: "compact K"
    and X_measurable: "X \<in> sets lborel"
  shows "\<exists>C::real. 0 < C \<and>
    (\<forall>tau c f epsilon orientation.
      2 \<le> tau \<and> slp_test_function_on K f \<and> epsilon \<in> {-1, 1}
      \<longrightarrow>
      slp_complex_lp_on s X
        (slp_cauchy_transform orientation
          (slp_oscillatory_modulation (epsilon * tau) c f)) \<and>
      slp_complex_lp_norm_on s X
        (slp_cauchy_transform orientation
          (slp_oscillatory_modulation (epsilon * tau) c f))
        \<le> C * inverse (sqrt tau) *
          slp_w1p_norm_on (slp_hls_source_exponent s) UNIV f (slp_classical_gradient f))"
proof -
  have s_positive: "0 < s" using s_lower by linarith
  have K_bounded: "bounded K"
    by (rule compact_imp_bounded[OF K_compact])
  obtain C::real where C_positive: "0 < C"
    and global_gain:
      "\<And>tau c f epsilon orientation.
        2 \<le> tau \<Longrightarrow> slp_test_function_on K f \<Longrightarrow>
        epsilon \<in> {-1, 1} \<Longrightarrow>
        aim_complex_lp_on_plane s
          (slp_cauchy_transform orientation
            (slp_oscillatory_modulation (epsilon * tau) c f)) \<and>
        aim_complex_lp_norm s
          (slp_cauchy_transform orientation
            (slp_oscillatory_modulation (epsilon * tau) c f))
          \<le> C * inverse (sqrt tau) *
            slp_w1p_norm_on (slp_hls_source_exponent s) UNIV f (slp_classical_gradient f)"
    using slp_uniform_terminal_w1p_gain_plane[OF s_lower K_bounded] by blast
  have local_gain:
      "slp_complex_lp_on s X
          (slp_cauchy_transform orientation
            (slp_oscillatory_modulation (epsilon * tau) c f)) \<and>
        slp_complex_lp_norm_on s X
          (slp_cauchy_transform orientation
            (slp_oscillatory_modulation (epsilon * tau) c f))
          \<le> C * inverse (sqrt tau) *
            slp_w1p_norm_on (slp_hls_source_exponent s) UNIV f (slp_classical_gradient f)"
    if tau_lower: "2 \<le> tau" and f_test: "slp_test_function_on K f"
      and epsilon_sign: "epsilon \<in> {-1, 1}"
    for tau :: real and c :: slp_point and f :: slp_scalar_field
      and epsilon :: real and orientation :: slp_cauchy_orientation
  proof -
    let ?T = "slp_cauchy_transform orientation
      (slp_oscillatory_modulation (epsilon * tau) c f)"
    note global_data = global_gain[OF tau_lower f_test epsilon_sign]
    have global_lp: "aim_complex_lp_on_plane s ?T"
      by (rule conjunct1[OF global_data])
    have local_lp: "slp_complex_lp_on s X ?T"
      by (rule aim_complex_lp_on_plane_restrict[OF s_positive X_measurable global_lp])
    have local_norm_le: "slp_complex_lp_norm_on s X ?T \<le> aim_complex_lp_norm s ?T"
      by (rule slp_complex_lp_norm_on_le[OF s_positive X_measurable global_lp])
    have local_bound:
        "slp_complex_lp_norm_on s X ?T \<le> C * inverse (sqrt tau) *
          slp_w1p_norm_on (slp_hls_source_exponent s) UNIV f (slp_classical_gradient f)"
      by (rule order_trans[OF local_norm_le conjunct2[OF global_data]])
    show ?thesis by (rule conjI[OF local_lp local_bound])
  qed
  show ?thesis
    by (rule exI[of _ C], rule conjI[OF C_positive])
      (use local_gain in blast)
qed

end

end
