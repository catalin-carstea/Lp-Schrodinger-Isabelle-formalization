theory Inverse_Schrodinger_Lp_Qstar_Centered_Cutoff_Source_Input_Lp
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_010.Inverse_Schrodinger_Lp_Complex_Lp_Real_Majorant"
begin

section \<open>Centered cutoff-derivative source in the HLS input space\<close>

context aim_planar_riesz_hls
begin

theorem slp_qstar_centered_cutoff_partial_source_input_complex_Lp:
  assumes exponent_lower: "1 < a"
    and exponent_upper: "a < 2"
    and delta_positive: "0 < delta"
    and amplitude_lp:
      "aim_complex_lp_on_plane (aim_hls_target_exponent a) f"
  shows source_lp:
      "aim_complex_lp_on_plane a
        (slp_qstar_centered_cutoff_partial_source delta f)"
    and source_norm_bound:
      "aim_complex_lp_norm a
          (slp_qstar_centered_cutoff_partial_source delta f) \<le>
        (slp_global_cutoff_L / delta) *
          ((integral\<^sup>L lborel
              (slp_squared_radial_annulus 1 2)) powr (1 / 2) *
            aim_complex_lp_norm (aim_hls_target_exponent a) f)"
proof -
  let ?q = "aim_hls_target_exponent a"
  let ?S = "slp_qstar_centered_cutoff_partial_source delta f"
  let ?I = "slp_qstar_annular_I2_source delta f"
  let ?k = "slp_global_cutoff_L / delta"
  have a_positive: "0 < a"
    using exponent_lower by linarith
  have amplitude_measurable: "f \<in> borel_measurable lborel"
    using amplitude_lp unfolding aim_complex_lp_on_plane_def by blast
  have I_lp: "aim_complex_lp_on_plane a ?I"
    by (rule slp_qstar_annular_I2_source_bound(3)[OF exponent_lower
          exponent_upper delta_positive amplitude_lp])
  have I_norm_bound:
      "aim_complex_lp_norm a ?I \<le>
        (integral\<^sup>L lborel
          (slp_squared_radial_annulus 1 2)) powr (1 / 2) *
        aim_complex_lp_norm ?q f"
    by (rule slp_qstar_annular_I2_source_bound(5)[OF exponent_lower
          exponent_upper delta_positive amplitude_lp])
  have I_measurable: "?I \<in> borel_measurable lborel"
    and I_power_integrable:
      "integrable lborel (\<lambda>y. norm (?I y) powr a)"
    using I_lp unfolding aim_complex_lp_on_plane_def by blast+
  have I_norm_measurable:
      "(\<lambda>y. norm (?I y)) \<in> borel_measurable lborel"
    using I_measurable by measurable
  have I_norm_power_integrable:
      "integrable lborel (\<lambda>y. abs (norm (?I y)) powr a)"
    using I_power_integrable by simp
  have I_norm_real_lp:
      "aim_real_lp_on_plane a (\<lambda>y. norm (?I y))"
    unfolding aim_real_lp_on_plane_def
    using I_norm_measurable I_norm_power_integrable by blast
  have k_nonnegative: "0 \<le> ?k"
    using slp_global_cutoff_profile_spec delta_positive by simp
  have majorant_lp:
      "aim_real_lp_on_plane a (\<lambda>y. ?k * norm (?I y))"
    by (rule slp_nonnegative_real_lp_scale(1)[OF a_positive
          k_nonnegative I_norm_real_lp])
  have source_measurable: "?S \<in> borel_measurable lborel"
    unfolding slp_qstar_centered_cutoff_partial_source_def
    using slp_qstar_cutoff_partial_coefficient_borel_measurable[of delta 0]
      amplitude_measurable
    apply measurable
    subgoal by (rule slp_point_as_complex_borel_measurable)
    subgoal by (rule amplitude_measurable)
    done
  have pointwise_bound: "\<And>y. norm (?S y) \<le> ?k * norm (?I y)"
  proof -
    fix y :: slp_point
    let ?D = "slp_real_wirtinger_partial
      (slp_global_cutoff.slp_scaled_cutoff_derivative delta 0 y)"
    have derivative_bound: "norm ?D \<le> ?k"
      by (rule slp_global_cutoff.slp_scaled_cutoff_partial_bound[OF
            delta_positive])
    show "norm (?S y) \<le> ?k * norm (?I y)"
    proof (cases "?D = 0")
      case True
      have source_zero: "?S y = 0"
        unfolding slp_qstar_centered_cutoff_partial_source_def
        by (simp only: True mult_zero_left)
      have right_nonnegative: "0 \<le> ?k * norm (?I y)"
        by (rule mult_nonneg_nonneg[OF k_nonnegative norm_ge_zero])
      show ?thesis
        unfolding source_zero norm_zero by (rule right_nonnegative)
    next
      case False
      have annulus:
          "delta \<le> norm y \<and> norm y \<le> 2 * delta"
        using slp_cutoff_profile.slp_scaled_cutoff_partial_support[OF
            slp_global_cutoff_profile_spec[THEN conjunct1]
            delta_positive False]
        by simp
      let ?B = "slp_radial_inverse y * norm (f y)"
      have base_nonnegative: "0 \<le> ?B"
        by (rule mult_nonneg_nonneg[OF
              slp_radial_inverse_nonnegative norm_ge_zero])
      have source_norm_value: "norm (?S y) = norm ?D * ?B"
        unfolding slp_qstar_centered_cutoff_partial_source_def
          slp_radial_inverse_def
        by (simp only: norm_mult norm_inverse
              slp_point_as_complex_norm mult.assoc)
      have carrier_norm_value: "norm (?I y) = ?B"
        unfolding slp_qstar_annular_I2_source_def
          slp_qstar_annular_I2_coefficient_def if_P[OF annulus]
        by (simp only: norm_mult norm_of_real abs_of_nonneg
              slp_radial_inverse_nonnegative)
      have "norm ?D * ?B \<le> ?k * ?B"
        by (rule mult_right_mono[OF derivative_bound base_nonnegative])
      then show ?thesis
        unfolding source_norm_value carrier_norm_value .
    qed
  qed
  have pointwise_bound_AE:
      "AE y in lborel. norm (?S y) \<le> ?k * norm (?I y)"
    using pointwise_bound by simp
  have source_data:
      "aim_complex_lp_on_plane a ?S \<and>
        aim_complex_lp_norm a ?S \<le>
          aim_real_lp_norm a (\<lambda>y. ?k * norm (?I y))"
    using slp_complex_lp_real_majorant[OF a_positive source_measurable
        majorant_lp pointwise_bound_AE] by blast
  show "aim_complex_lp_on_plane a ?S"
    using source_data by blast
  have majorant_norm:
      "aim_real_lp_norm a (\<lambda>y. ?k * norm (?I y)) =
        ?k * aim_complex_lp_norm a ?I"
  proof -
    have scaled:
        "aim_real_lp_norm a (\<lambda>y. ?k * norm (?I y)) =
          ?k * aim_real_lp_norm a (\<lambda>y. norm (?I y))"
      by (rule slp_nonnegative_real_lp_scale(2)[OF a_positive
            k_nonnegative I_norm_real_lp])
    have norm_identity:
        "aim_real_lp_norm a (\<lambda>y. norm (?I y)) =
          aim_complex_lp_norm a ?I"
      unfolding aim_real_lp_norm_def aim_complex_lp_norm_def by simp
    show ?thesis
      unfolding scaled norm_identity by (rule refl)
  qed
  have scaled_I_bound:
      "?k * aim_complex_lp_norm a ?I \<le>
        ?k *
          ((integral\<^sup>L lborel
              (slp_squared_radial_annulus 1 2)) powr (1 / 2) *
            aim_complex_lp_norm ?q f)"
    by (rule mult_left_mono[OF I_norm_bound k_nonnegative])
  show "aim_complex_lp_norm a ?S \<le>
      ?k *
        ((integral\<^sup>L lborel
            (slp_squared_radial_annulus 1 2)) powr (1 / 2) *
          aim_complex_lp_norm ?q f)"
    using source_data majorant_norm scaled_I_bound by linarith
qed

end

end
