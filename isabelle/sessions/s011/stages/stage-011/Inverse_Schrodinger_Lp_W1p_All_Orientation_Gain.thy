theory Inverse_Schrodinger_Lp_W1p_All_Orientation_Gain
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_011.Inverse_Schrodinger_Lp_W1p_Negative_Psi_Gains"
begin

section \<open>One rough Sobolev gain for both signs and orientations\<close>

context slp_qstar_centered_smooth_far_hls_context
begin

theorem slp_w1p_zero_pair_all_orientation_gain:
  assumes a_lower: "1 < a" and a_upper: "a < 2" and X_bounded: "bounded X"
  shows "\<exists>C::real. 0 < C \<and>
    (\<forall>tau c f Df epsilon orientation.
      2 \<le> tau \<and> slp_w1p_zero_pair_on a X f Df \<and>
        epsilon \<in> {-1, 1} \<longrightarrow>
      aim_complex_lp_on_plane (aim_hls_target_exponent a)
        (slp_cauchy_transform orientation
          (slp_oscillatory_modulation (epsilon * tau) c (slp_restrict_field X f))) \<and>
      aim_complex_lp_norm (aim_hls_target_exponent a)
        (slp_cauchy_transform orientation
          (slp_oscillatory_modulation (epsilon * tau) c (slp_restrict_field X f)))
        \<le> C * inverse (sqrt tau) * slp_w1p_norm_on a X f Df)"
proof -
  let ?G = "\<lambda>orientation epsilon C.
    \<forall>tau c f Df. 2 \<le> tau \<and> slp_w1p_zero_pair_on a X f Df \<longrightarrow>
      aim_complex_lp_on_plane (aim_hls_target_exponent a)
        (slp_cauchy_transform orientation
          (slp_oscillatory_modulation (epsilon * tau) c (slp_restrict_field X f))) \<and>
      aim_complex_lp_norm (aim_hls_target_exponent a)
        (slp_cauchy_transform orientation
          (slp_oscillatory_modulation (epsilon * tau) c (slp_restrict_field X f)))
        \<le> C * inverse (sqrt tau) * slp_w1p_norm_on a X f Df"
  obtain Cp::real where Cp_positive: "0 < Cp"
    and Cp_gain: "?G SLP_Partial_Inverse 1 Cp"
    using slp_w1p_zero_pair_partial_psi_gain[OF a_lower a_upper X_bounded]
    by (auto simp: slp_partial_psi_inverse_def)
  obtain Cm::real where Cm_positive: "0 < Cm"
    and Cm_gain: "?G SLP_Partial_Inverse (-1) Cm"
    using slp_w1p_zero_pair_negative_partial_psi_gain[OF a_lower a_upper X_bounded]
    by (auto simp: slp_partial_psi_inverse_def)
  obtain Dp::real where Dp_positive: "0 < Dp"
    and Dp_gain: "?G SLP_Dbar_Inverse 1 Dp"
    using slp_w1p_zero_pair_negative_dbar_psi_gain[OF a_lower a_upper X_bounded]
    by (auto simp: slp_dbar_psi_inverse_def)
  obtain Dm::real where Dm_positive: "0 < Dm"
    and Dm_gain: "?G SLP_Dbar_Inverse (-1) Dm"
    using slp_w1p_zero_pair_dbar_psi_gain[OF a_lower a_upper X_bounded]
    by (auto simp: slp_dbar_psi_inverse_def)
  let ?C = "Cp + Cm + Dp + Dm"
  have C_positive: "0 < ?C"
    using Cp_positive Cm_positive Dp_positive Dm_positive by linarith
  have Cp_le: "Cp \<le> ?C" and Cm_le: "Cm \<le> ?C"
    and Dp_le: "Dp \<le> ?C" and Dm_le: "Dm \<le> ?C"
    using Cp_positive Cm_positive Dp_positive Dm_positive by linarith+
  have enlarge: "?G orientation epsilon ?C"
    if base: "?G orientation epsilon K" and K_le: "K \<le> ?C"
    for orientation epsilon K
  proof (intro allI impI)
    fix tau :: real and c :: slp_point
      and f :: slp_scalar_field and Df :: slp_gradient_field
    assume data: "2 \<le> tau \<and> slp_w1p_zero_pair_on a X f Df"
    let ?T = "slp_cauchy_transform orientation
      (slp_oscillatory_modulation (epsilon * tau) c (slp_restrict_field X f))"
    have output_lp: "aim_complex_lp_on_plane (aim_hls_target_exponent a) ?T"
      and output_bound:
        "aim_complex_lp_norm (aim_hls_target_exponent a) ?T
          \<le> K * inverse (sqrt tau) * slp_w1p_norm_on a X f Df"
      using base data by blast+
    have tau_nonnegative: "0 \<le> tau" using data by linarith
    have factor_nonnegative: "0 \<le> inverse (sqrt tau)"
      using tau_nonnegative by simp
    have norm_nonnegative: "0 \<le> slp_w1p_norm_on a X f Df"
      by (simp add: slp_w1p_norm_on_def)
    have bound_enlarged:
        "K * inverse (sqrt tau) * slp_w1p_norm_on a X f Df
          \<le> ?C * inverse (sqrt tau) * slp_w1p_norm_on a X f Df"
      by (rule mult_right_mono[
            OF mult_right_mono[OF K_le factor_nonnegative] norm_nonnegative])
    have final_bound:
        "aim_complex_lp_norm (aim_hls_target_exponent a) ?T
          \<le> ?C * inverse (sqrt tau) * slp_w1p_norm_on a X f Df"
      by (rule order_trans[OF output_bound bound_enlarged])
    show "aim_complex_lp_on_plane (aim_hls_target_exponent a) ?T \<and>
      aim_complex_lp_norm (aim_hls_target_exponent a) ?T
        \<le> ?C * inverse (sqrt tau) * slp_w1p_norm_on a X f Df"
      by (rule conjI[OF output_lp final_bound])
  qed
  note common_Cp = enlarge[OF Cp_gain Cp_le]
  note common_Cm = enlarge[OF Cm_gain Cm_le]
  note common_Dp = enlarge[OF Dp_gain Dp_le]
  note common_Dm = enlarge[OF Dm_gain Dm_le]
  have all_cases: "?G orientation epsilon ?C"
    if "epsilon \<in> {-1, 1}" for orientation epsilon
    using that common_Cp common_Cm common_Dp common_Dm
    by (cases orientation) auto
  show ?thesis
    by (rule exI[of _ ?C], rule conjI[OF C_positive])
      (use all_cases in blast)
qed

end

end
