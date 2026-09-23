theory Inverse_Schrodinger_Lp_Qstar_Square_Denominator_Complex_Lp
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_009.Inverse_Schrodinger_Lp_Qstar_Square_Denominator_Integral"
begin

hide_const (open) Commutative_Ring.norm

section \<open>The centered square-denominator complex Lp bound\<close>

context aim_planar_riesz_hls
begin

theorem slp_qstar_square_denominator_integral_complex_Lp:
  "\<exists>C::real. 0 < C \<and>
    (\<forall>a delta R f. 1 < a \<and> a < 2 \<and> 0 < delta \<and>
        delta \<le> R \<and>
        aim_complex_lp_on_plane (aim_hls_target_exponent a) f \<and>
        (\<forall>y. f y \<noteq> 0 \<longrightarrow> norm y \<le> R)
      \<longrightarrow>
      aim_complex_lp_on_plane (aim_hls_target_exponent a)
        (slp_qstar_square_denominator_integral delta f) \<and>
      aim_complex_lp_norm (aim_hls_target_exponent a)
          (slp_qstar_square_denominator_integral delta f) \<le>
        4 *
          ((1 / delta) *
              integral\<^sup>L lborel (slp_localized_cauchy_kernel 1) *
              aim_complex_lp_norm (aim_hls_target_exponent a) f +
           C / ((a - 1) * (2 - a)) * (1 / delta) *
              slp_qstar_annular_J2_unit_coefficient_mass powr (1 / 2) *
              aim_complex_lp_norm (aim_hls_target_exponent a) f))"
proof -
  obtain C::real where C_positive: "0 < C"
    and J12_bound:
      "\<And>a delta R f. 1 < a \<Longrightarrow> a < 2 \<Longrightarrow>
        0 < delta \<Longrightarrow> delta \<le> R \<Longrightarrow>
        aim_complex_lp_on_plane (aim_hls_target_exponent a) f \<Longrightarrow>
        aim_real_lp_on_plane (aim_hls_target_exponent a)
          (slp_qstar_annular_J12_potential delta R f) \<and>
        aim_real_lp_norm (aim_hls_target_exponent a)
            (slp_qstar_annular_J12_potential delta R f) \<le>
          4 *
            ((1 / delta) *
                integral\<^sup>L lborel (slp_localized_cauchy_kernel 1) *
                aim_complex_lp_norm (aim_hls_target_exponent a) f +
             C / ((a - 1) * (2 - a)) * (1 / delta) *
                slp_qstar_annular_J2_unit_coefficient_mass powr (1 / 2) *
                aim_complex_lp_norm (aim_hls_target_exponent a) f)"
    using slp_qstar_annular_J12_combined by blast
  have all_outputs:
    "\<forall>a delta R f. 1 < a \<and> a < 2 \<and> 0 < delta \<and>
        delta \<le> R \<and>
        aim_complex_lp_on_plane (aim_hls_target_exponent a) f \<and>
        (\<forall>y. f y \<noteq> 0 \<longrightarrow> norm y \<le> R)
      \<longrightarrow>
      aim_complex_lp_on_plane (aim_hls_target_exponent a)
        (slp_qstar_square_denominator_integral delta f) \<and>
      aim_complex_lp_norm (aim_hls_target_exponent a)
          (slp_qstar_square_denominator_integral delta f) \<le>
        4 *
          ((1 / delta) *
              integral\<^sup>L lborel (slp_localized_cauchy_kernel 1) *
              aim_complex_lp_norm (aim_hls_target_exponent a) f +
           C / ((a - 1) * (2 - a)) * (1 / delta) *
              slp_qstar_annular_J2_unit_coefficient_mass powr (1 / 2) *
              aim_complex_lp_norm (aim_hls_target_exponent a) f)"
  proof (intro allI impI)
    fix a delta R :: real and f :: slp_scalar_field
    assume hypotheses:
      "1 < a \<and> a < 2 \<and> 0 < delta \<and> delta \<le> R \<and>
        aim_complex_lp_on_plane (aim_hls_target_exponent a) f \<and>
        (\<forall>y. f y \<noteq> 0 \<longrightarrow> norm y \<le> R)"
    have exponent_lower: "1 < a" and exponent_upper: "a < 2"
      and delta_positive: "0 < delta" and radius_lower: "delta \<le> R"
      using hypotheses by blast+
    have amplitude_lp:
        "aim_complex_lp_on_plane (aim_hls_target_exponent a) f"
      using hypotheses by blast
    have amplitude_radius: "\<And>y. f y \<noteq> 0 \<Longrightarrow> norm y \<le> R"
      using hypotheses by blast
    let ?q = "aim_hls_target_exponent a"
    let ?T = "slp_qstar_square_denominator_integral delta f"
    let ?J = "slp_qstar_annular_J12_potential delta R f"
    let ?B = "4 *
      ((1 / delta) *
          integral\<^sup>L lborel (slp_localized_cauchy_kernel 1) *
          aim_complex_lp_norm ?q f +
       C / ((a - 1) * (2 - a)) * (1 / delta) *
          slp_qstar_annular_J2_unit_coefficient_mass powr (1 / 2) *
          aim_complex_lp_norm ?q f)"
    have q_above_two: "2 < ?q"
      by (rule slp_qstar_exponent_relations(1)[OF exponent_lower
            exponent_upper])
    have q_positive: "0 < ?q"
      using q_above_two by linarith
    have integral_data:
        "?T \<in> borel_measurable lborel \<and>
        (AE z in lborel. integrable lborel
          (slp_qstar_square_denominator_integrand delta f z)) \<and>
        (AE z in lborel. norm (?T z) \<le> ?J z)"
      using slp_qstar_square_denominator_integral_bound[OF exponent_lower
          exponent_upper delta_positive radius_lower amplitude_lp
          amplitude_radius] by blast
    have output_measurable: "?T \<in> borel_measurable lborel"
      using integral_data by blast
    have pointwise_bound: "AE z in lborel. norm (?T z) \<le> ?J z"
      using integral_data by blast
    have J12_data:
        "aim_real_lp_on_plane ?q ?J \<and>
        aim_real_lp_norm ?q ?J \<le> ?B"
      by (rule J12_bound[OF exponent_lower exponent_upper delta_positive
            radius_lower amplitude_lp])
    have J12_lp: "aim_real_lp_on_plane ?q ?J"
      using J12_data by blast
    have J12_norm: "aim_real_lp_norm ?q ?J \<le> ?B"
      using J12_data by blast
    let ?u = "\<lambda>z. norm (?T z)"
    have output_norm_measurable: "?u \<in> borel_measurable lborel"
      using output_measurable by measurable
    have output_norm_nonnegative: "AE z in lborel. 0 \<le> ?u z"
      by simp
    have output_norm_lp: "aim_real_lp_on_plane ?q ?u"
      by (rule slp_nonnegative_real_lp_mono(1)[OF q_positive
            output_norm_measurable J12_lp output_norm_nonnegative
            pointwise_bound])
    have output_norm_bound:
        "aim_real_lp_norm ?q ?u \<le> aim_real_lp_norm ?q ?J"
      by (rule slp_nonnegative_real_lp_mono(2)[OF q_positive
            output_norm_measurable J12_lp output_norm_nonnegative
            pointwise_bound])
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
        "aim_complex_lp_norm ?q ?T \<le> ?B"
      unfolding norm_identity
      by (rule order_trans[OF output_norm_bound J12_norm])
    show "aim_complex_lp_on_plane ?q ?T \<and>
        aim_complex_lp_norm ?q ?T \<le> ?B"
      using output_complex_lp output_complex_norm by blast
  qed
  show ?thesis
    using C_positive all_outputs by blast
qed

end

end
