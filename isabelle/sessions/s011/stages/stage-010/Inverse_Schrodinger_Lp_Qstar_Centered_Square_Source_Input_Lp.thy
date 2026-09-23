theory Inverse_Schrodinger_Lp_Qstar_Centered_Square_Source_Input_Lp
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_010.Inverse_Schrodinger_Lp_Qstar_Centered_Cutoff_Source_Input_Lp"
begin

section \<open>Centered square-denominator source in the HLS input space\<close>

context aim_planar_riesz_hls
begin

theorem slp_qstar_centered_square_denominator_source_input_complex_Lp:
  assumes exponent_lower: "1 < a"
    and exponent_upper: "a < 2"
    and delta_positive: "0 < delta"
    and radius_lower: "delta \<le> R"
    and amplitude_lp:
      "aim_complex_lp_on_plane (aim_hls_target_exponent a) f"
    and amplitude_radius: "\<And>y. f y \<noteq> 0 \<Longrightarrow> norm y \<le> R"
  shows source_lp:
      "aim_complex_lp_on_plane a
        (slp_qstar_centered_square_denominator_source delta f)"
    and source_norm_bound:
      "aim_complex_lp_norm a
          (slp_qstar_centered_square_denominator_source delta f) \<le>
        (1 / delta) *
          slp_qstar_annular_J2_unit_coefficient_mass powr (1 / 2) *
          aim_complex_lp_norm (aim_hls_target_exponent a) f"
proof -
  let ?q = "aim_hls_target_exponent a"
  let ?S = "slp_qstar_centered_square_denominator_source delta f"
  let ?J = "slp_qstar_annular_J2_source delta R f"
  have a_positive: "0 < a"
    using exponent_lower by linarith
  have amplitude_measurable: "f \<in> borel_measurable lborel"
    using amplitude_lp unfolding aim_complex_lp_on_plane_def by blast
  have J_lp: "aim_complex_lp_on_plane a ?J"
    by (rule slp_qstar_annular_J2_source_bound(4)[OF exponent_lower
          exponent_upper delta_positive radius_lower amplitude_lp])
  have J_norm_bound:
      "aim_complex_lp_norm a ?J \<le>
        (1 / delta) *
          slp_qstar_annular_J2_unit_coefficient_mass powr (1 / 2) *
          aim_complex_lp_norm ?q f"
    by (rule slp_qstar_annular_J2_source_bound(6)[OF exponent_lower
          exponent_upper delta_positive radius_lower amplitude_lp])
  have J_measurable: "?J \<in> borel_measurable lborel"
    and J_power_integrable:
      "integrable lborel (\<lambda>y. norm (?J y) powr a)"
    using J_lp unfolding aim_complex_lp_on_plane_def by blast+
  have J_norm_measurable:
      "(\<lambda>y. norm (?J y)) \<in> borel_measurable lborel"
    using J_measurable by measurable
  have J_norm_power_integrable:
      "integrable lborel (\<lambda>y. abs (norm (?J y)) powr a)"
    using J_power_integrable by simp
  have J_norm_real_lp:
      "aim_real_lp_on_plane a (\<lambda>y. norm (?J y))"
    unfolding aim_real_lp_on_plane_def
    using J_norm_measurable J_norm_power_integrable by blast
  have cutoff_measurable:
      "slp_global_cutoff.slp_scaled_cutoff delta 0 \<in>
        borel_measurable lborel"
    using slp_global_scaled_cutoff_borel_measurable[of delta 0]
    unfolding slp_global_scaled_cutoff_def .
  have source_measurable: "?S \<in> borel_measurable lborel"
    unfolding slp_qstar_centered_square_denominator_source_def
    using cutoff_measurable amplitude_measurable
    apply measurable
    subgoal by (rule slp_point_as_complex_borel_measurable)
    subgoal by (rule amplitude_measurable)
    done
  have pointwise_bound: "\<And>y. norm (?S y) \<le> norm (?J y)"
  proof -
    fix y :: slp_point
    let ?cutoff = "slp_global_cutoff.slp_scaled_cutoff delta 0 y"
    show "norm (?S y) \<le> norm (?J y)"
    proof (cases "f y = 0 \<or> 1 - ?cutoff = 0")
      case True
      have source_zero: "?S y = 0"
      proof (rule disjE[OF True])
        assume amplitude_zero: "f y = 0"
        show ?thesis
          unfolding slp_qstar_centered_square_denominator_source_def
            amplitude_zero
          by (simp only: mult_zero_right)
      next
        assume complement_zero: "1 - ?cutoff = 0"
        show ?thesis
          unfolding slp_qstar_centered_square_denominator_source_def
            complement_zero
          by (simp only: of_real_0 mult_zero_left)
      qed
      show ?thesis
        unfolding source_zero norm_zero by (rule norm_ge_zero)
    next
      case False
      have amplitude_nonzero: "f y \<noteq> 0"
        using False by blast
      have complement_nonzero: "1 - ?cutoff \<noteq> 0"
        using False by blast
      have annular_lower: "delta \<le> norm y"
      proof -
        have strict: "delta < norm (y - (0 :: slp_point))"
          using slp_cutoff_profile.slp_scaled_cutoff_complement_support[
            OF slp_global_cutoff_profile_spec[THEN conjunct1]
              delta_positive complement_nonzero] .
        then show ?thesis by simp
      qed
      have annular_upper: "norm y \<le> R"
        by (rule amplitude_radius[OF amplitude_nonzero])
      have annulus: "delta \<le> norm y \<and> norm y \<le> R"
        using annular_lower annular_upper by blast
      have cutoff_nonnegative: "0 \<le> ?cutoff"
        unfolding slp_global_cutoff.slp_scaled_cutoff_def
        using slp_global_cutoff_profile_spec by blast
      have cutoff_at_most_one: "?cutoff \<le> 1"
        unfolding slp_global_cutoff.slp_scaled_cutoff_def
        using slp_global_cutoff_profile_spec by blast
      have complement_nonnegative: "0 \<le> 1 - ?cutoff"
        using cutoff_at_most_one by linarith
      have complement_at_most_one: "1 - ?cutoff \<le> 1"
        using cutoff_nonnegative by linarith
      have complement_norm_bound:
          "norm (of_real (1 - ?cutoff) :: complex) \<le> 1"
        by (simp only: norm_of_real abs_of_nonneg[OF complement_nonnegative]
              complement_at_most_one)
      let ?B = "slp_radial_inverse_square y * norm (f y)"
      have base_nonnegative: "0 \<le> ?B"
        by (rule mult_nonneg_nonneg[OF
              slp_radial_inverse_square_nonnegative norm_ge_zero])
      have source_norm_value:
          "norm (?S y) =
            norm (of_real (1 - ?cutoff) :: complex) * ?B"
        unfolding slp_qstar_centered_square_denominator_source_def
          slp_radial_inverse_square_def slp_radial_inverse_def
        by (simp only: norm_mult norm_power norm_inverse
              slp_point_as_complex_norm mult.assoc)
      have carrier_norm_value: "norm (?J y) = ?B"
        unfolding slp_qstar_annular_J2_source_def
          slp_qstar_annular_J2_coefficient_def if_P[OF annulus]
        by (simp only: norm_mult norm_of_real abs_of_nonneg
              slp_radial_inverse_square_nonnegative)
      have
          "norm (of_real (1 - ?cutoff) :: complex) * ?B \<le> 1 * ?B"
        by (rule mult_right_mono[OF complement_norm_bound base_nonnegative])
      then show ?thesis
        unfolding source_norm_value carrier_norm_value by simp
    qed
  qed
  have pointwise_bound_AE: "AE y in lborel. norm (?S y) \<le> norm (?J y)"
    using pointwise_bound by simp
  have source_data:
      "aim_complex_lp_on_plane a ?S \<and>
        aim_complex_lp_norm a ?S \<le>
          aim_real_lp_norm a (\<lambda>y. norm (?J y))"
    using slp_complex_lp_real_majorant[OF a_positive source_measurable
        J_norm_real_lp pointwise_bound_AE] by blast
  show "aim_complex_lp_on_plane a ?S"
    using source_data by blast
  have norm_identity:
      "aim_real_lp_norm a (\<lambda>y. norm (?J y)) =
        aim_complex_lp_norm a ?J"
    unfolding aim_real_lp_norm_def aim_complex_lp_norm_def by simp
  show "aim_complex_lp_norm a ?S \<le>
      (1 / delta) *
        slp_qstar_annular_J2_unit_coefficient_mass powr (1 / 2) *
        aim_complex_lp_norm ?q f"
    using source_data norm_identity J_norm_bound by linarith
qed

end

end
