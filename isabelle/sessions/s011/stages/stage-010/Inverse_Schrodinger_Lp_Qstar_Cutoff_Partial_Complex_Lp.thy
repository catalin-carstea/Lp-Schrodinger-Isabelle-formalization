theory Inverse_Schrodinger_Lp_Qstar_Cutoff_Partial_Complex_Lp
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_010.Inverse_Schrodinger_Lp_Qstar_Cutoff_Partial_Integral"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_009.Inverse_Schrodinger_Lp_Qstar_Annular_J2_Riesz_HLS"
begin

hide_const (open) Commutative_Ring.norm

section \<open>The centered cutoff-partial complex Lp bound\<close>

lemma slp_nonnegative_real_lp_scale:
  assumes exponent_positive: "0 < p"
    and scalar_nonnegative: "0 \<le> c"
    and function_lp: "aim_real_lp_on_plane p u"
  shows scaled_lp:
      "aim_real_lp_on_plane p (\<lambda>x. c * u x)"
    and scaled_norm:
      "aim_real_lp_norm p (\<lambda>x. c * u x) =
        c * aim_real_lp_norm p u"
proof -
  have function_measurable: "u \<in> borel_measurable lborel"
    and function_power_integrable:
      "integrable lborel (\<lambda>x. abs (u x) powr p)"
    using function_lp unfolding aim_real_lp_on_plane_def by blast+
  have scaled_measurable:
      "(\<lambda>x. c * u x) \<in> borel_measurable lborel"
    using function_measurable by measurable
  have power_presentation:
      "(\<lambda>x. abs (c * u x) powr p) =
        (\<lambda>x. c powr p * abs (u x) powr p)"
  proof (rule ext)
    fix x
    have absolute_scalar: "abs c = c"
      by (rule abs_of_nonneg[OF scalar_nonnegative])
    show "abs (c * u x) powr p =
        c powr p * abs (u x) powr p"
      by (simp only: abs_mult absolute_scalar powr_mult)
  qed
  have scaled_power_integrable:
      "integrable lborel (\<lambda>x. abs (c * u x) powr p)"
    unfolding power_presentation
    using function_power_integrable by simp
  show "aim_real_lp_on_plane p (\<lambda>x. c * u x)"
    unfolding aim_real_lp_on_plane_def
    using scaled_measurable scaled_power_integrable by blast
  let ?A = "integral\<^sup>L lborel (\<lambda>x. abs (u x) powr p)"
  have A_nonnegative: "0 \<le> ?A"
    by (rule integral_nonneg_AE) simp
  have scaled_integral:
      "integral\<^sup>L lborel (\<lambda>x. abs (c * u x) powr p) =
        c powr p * ?A"
    unfolding power_presentation
    using function_power_integrable by simp
  have exponent_nonzero: "p \<noteq> 0"
    using exponent_positive by simp
  show "aim_real_lp_norm p (\<lambda>x. c * u x) =
      c * aim_real_lp_norm p u"
    unfolding aim_real_lp_norm_def scaled_integral
    using scalar_nonnegative A_nonnegative exponent_nonzero
    by (simp add: powr_mult powr_powr)
qed

context aim_planar_riesz_hls
begin

theorem slp_qstar_cutoff_partial_integral_complex_Lp:
  "\<exists>C::real. 0 < C \<and>
    (\<forall>a delta f. 1 < a \<and> a < 2 \<and> 0 < delta \<and>
        aim_complex_lp_on_plane (aim_hls_target_exponent a) f
      \<longrightarrow>
      aim_complex_lp_on_plane (aim_hls_target_exponent a)
        (slp_qstar_cutoff_partial_integral delta f) \<and>
      aim_complex_lp_norm (aim_hls_target_exponent a)
          (slp_qstar_cutoff_partial_integral delta f) \<le>
        (slp_global_cutoff_L / delta) * 4 *
          ((9 * pi) powr (1 / aim_hls_target_exponent a) *
            (integral\<^sup>L lborel
              (\<lambda>x. abs (slp_localized_cauchy_kernel 1 x) powr
                slp_qstar_holder_exponent a))
              powr (1 / slp_qstar_holder_exponent a) *
            aim_complex_lp_norm (aim_hls_target_exponent a) f +
           C / ((a - 1) * (2 - a)) *
            (integral\<^sup>L lborel
              (slp_squared_radial_annulus 1 2)) powr (1 / 2) *
            aim_complex_lp_norm (aim_hls_target_exponent a) f))"
proof -
  obtain C::real where C_positive: "0 < C"
    and annular_bound:
      "\<And>a delta f. 1 < a \<Longrightarrow> a < 2 \<Longrightarrow>
        0 < delta \<Longrightarrow>
        aim_complex_lp_on_plane (aim_hls_target_exponent a) f \<Longrightarrow>
        aim_real_lp_on_plane (aim_hls_target_exponent a)
          (slp_qstar_annular_combined_potential delta f) \<and>
        aim_real_lp_norm (aim_hls_target_exponent a)
            (slp_qstar_annular_combined_potential delta f) \<le>
          4 *
            ((9 * pi) powr (1 / aim_hls_target_exponent a) *
              (integral\<^sup>L lborel
                (\<lambda>x. abs (slp_localized_cauchy_kernel 1 x) powr
                  slp_qstar_holder_exponent a))
                powr (1 / slp_qstar_holder_exponent a) *
              aim_complex_lp_norm (aim_hls_target_exponent a) f +
             C / ((a - 1) * (2 - a)) *
              (integral\<^sup>L lborel
                (slp_squared_radial_annulus 1 2)) powr (1 / 2) *
              aim_complex_lp_norm (aim_hls_target_exponent a) f)"
    using slp_qstar_annular_combined_delta_independent by blast
  have all_outputs:
    "\<forall>a delta f. 1 < a \<and> a < 2 \<and> 0 < delta \<and>
        aim_complex_lp_on_plane (aim_hls_target_exponent a) f
      \<longrightarrow>
      aim_complex_lp_on_plane (aim_hls_target_exponent a)
        (slp_qstar_cutoff_partial_integral delta f) \<and>
      aim_complex_lp_norm (aim_hls_target_exponent a)
          (slp_qstar_cutoff_partial_integral delta f) \<le>
        (slp_global_cutoff_L / delta) * 4 *
          ((9 * pi) powr (1 / aim_hls_target_exponent a) *
            (integral\<^sup>L lborel
              (\<lambda>x. abs (slp_localized_cauchy_kernel 1 x) powr
                slp_qstar_holder_exponent a))
              powr (1 / slp_qstar_holder_exponent a) *
            aim_complex_lp_norm (aim_hls_target_exponent a) f +
           C / ((a - 1) * (2 - a)) *
            (integral\<^sup>L lborel
              (slp_squared_radial_annulus 1 2)) powr (1 / 2) *
            aim_complex_lp_norm (aim_hls_target_exponent a) f)"
  proof (intro allI impI)
    fix a delta :: real and f :: slp_scalar_field
    assume hypotheses:
      "1 < a \<and> a < 2 \<and> 0 < delta \<and>
        aim_complex_lp_on_plane (aim_hls_target_exponent a) f"
    have exponent_lower: "1 < a" and exponent_upper: "a < 2"
      and delta_positive: "0 < delta"
      and amplitude_lp:
        "aim_complex_lp_on_plane (aim_hls_target_exponent a) f"
      using hypotheses by blast+
    let ?q = "aim_hls_target_exponent a"
    let ?k = "slp_global_cutoff_L / delta"
    let ?T = "slp_qstar_cutoff_partial_integral delta f"
    let ?J = "slp_qstar_annular_combined_potential delta f"
    let ?P =
      "(9 * pi) powr (1 / ?q) *
        (integral\<^sup>L lborel
          (\<lambda>x. abs (slp_localized_cauchy_kernel 1 x) powr
            slp_qstar_holder_exponent a))
          powr (1 / slp_qstar_holder_exponent a) *
        aim_complex_lp_norm ?q f +
       C / ((a - 1) * (2 - a)) *
        (integral\<^sup>L lborel
          (slp_squared_radial_annulus 1 2)) powr (1 / 2) *
        aim_complex_lp_norm ?q f"
    let ?B = "4 * ?P"
    have q_above_two: "2 < ?q"
      by (rule slp_qstar_exponent_relations(1)[OF exponent_lower
            exponent_upper])
    have q_positive: "0 < ?q"
      using q_above_two by linarith
    have coefficient_nonnegative: "0 \<le> ?k"
      using slp_global_cutoff_profile_spec delta_positive by simp
    have raw_data:
        "?T \<in> borel_measurable lborel \<and>
        (AE z in lborel. integrable lborel
          (slp_qstar_cutoff_partial_integrand delta f z)) \<and>
        (AE z in lborel. norm (?T z) \<le> ?k * ?J z)"
      using slp_qstar_cutoff_partial_integral_bound[OF exponent_lower
          exponent_upper delta_positive amplitude_lp] by blast
    have output_measurable: "?T \<in> borel_measurable lborel"
      using raw_data by blast
    have pointwise_bound: "AE z in lborel. norm (?T z) \<le> ?k * ?J z"
      using raw_data by blast
    have J_data:
        "aim_real_lp_on_plane ?q ?J \<and>
        aim_real_lp_norm ?q ?J \<le> ?B"
      by (rule annular_bound[OF exponent_lower exponent_upper
            delta_positive amplitude_lp])
    have J_lp: "aim_real_lp_on_plane ?q ?J"
      using J_data by blast
    have J_norm: "aim_real_lp_norm ?q ?J \<le> ?B"
      using J_data by blast
    let ?M = "\<lambda>z. ?k * ?J z"
    have scaled_data:
        "aim_real_lp_on_plane ?q ?M \<and>
        aim_real_lp_norm ?q ?M = ?k * aim_real_lp_norm ?q ?J"
      using slp_nonnegative_real_lp_scale[OF q_positive
          coefficient_nonnegative J_lp] by blast
    have majorant_lp: "aim_real_lp_on_plane ?q ?M"
      using scaled_data by blast
    have majorant_norm:
        "aim_real_lp_norm ?q ?M = ?k * aim_real_lp_norm ?q ?J"
      using scaled_data by blast
    let ?u = "\<lambda>z. norm (?T z)"
    have output_norm_measurable: "?u \<in> borel_measurable lborel"
      using output_measurable by measurable
    have output_norm_nonnegative: "AE z in lborel. 0 \<le> ?u z"
      by simp
    have output_norm_lp: "aim_real_lp_on_plane ?q ?u"
      by (rule slp_nonnegative_real_lp_mono(1)[OF q_positive
            output_norm_measurable majorant_lp output_norm_nonnegative
            pointwise_bound])
    have output_norm_bound:
        "aim_real_lp_norm ?q ?u \<le> aim_real_lp_norm ?q ?M"
      by (rule slp_nonnegative_real_lp_mono(2)[OF q_positive
            output_norm_measurable majorant_lp output_norm_nonnegative
            pointwise_bound])
    have scaled_J_bound:
        "?k * aim_real_lp_norm ?q ?J \<le> ?k * ?B"
      by (rule mult_left_mono[OF J_norm coefficient_nonnegative])
    have output_bound: "aim_real_lp_norm ?q ?u \<le> ?k * ?B"
      by (rule order_trans[OF output_norm_bound])
        (use majorant_norm scaled_J_bound in simp)
    have output_norm_power_integrable:
        "integrable lborel (\<lambda>z. abs (?u z) powr ?q)"
      using output_norm_lp unfolding aim_real_lp_on_plane_def by blast
    have output_power_integrable:
        "integrable lborel (\<lambda>z. norm (?T z) powr ?q)"
      using output_norm_power_integrable by simp
    have output_complex_lp: "aim_complex_lp_on_plane ?q ?T"
      unfolding aim_complex_lp_on_plane_def
      using output_measurable output_power_integrable by blast
    have norm_identity:
        "aim_complex_lp_norm ?q ?T = aim_real_lp_norm ?q ?u"
      unfolding aim_complex_lp_norm_def aim_real_lp_norm_def by simp
    have output_complex_norm:
        "aim_complex_lp_norm ?q ?T \<le> ?k * ?B"
      unfolding norm_identity by (rule output_bound)
    have output_complex_norm_outer:
        "aim_complex_lp_norm ?q ?T \<le> ?k * 4 * ?P"
      using output_complex_norm by (simp only: mult.assoc)
    show "aim_complex_lp_on_plane ?q ?T \<and>
        aim_complex_lp_norm ?q ?T \<le> ?k * 4 * ?P"
      by (rule conjI[OF output_complex_lp output_complex_norm_outer])
  qed
  show ?thesis
    using C_positive all_outputs by blast
qed

end

end
