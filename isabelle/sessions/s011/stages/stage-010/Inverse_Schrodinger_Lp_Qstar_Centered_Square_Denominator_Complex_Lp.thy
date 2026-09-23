theory Inverse_Schrodinger_Lp_Qstar_Centered_Square_Denominator_Complex_Lp
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_010.Inverse_Schrodinger_Lp_Qstar_Centered_Cutoff_Partial_Complex_Lp"
begin

section \<open>Centered square-denominator partial-Cauchy Lp bound\<close>

context aim_planar_riesz_hls
begin

theorem slp_qstar_centered_square_denominator_source_complex_Lp:
  "\<exists>C::real. 0 < C \<and>
    (\<forall>a tau delta R f.
      1 < a \<and> a < 2 \<and> 0 < delta \<and> delta \<le> R \<and>
      aim_complex_lp_on_plane (aim_hls_target_exponent a) f \<and>
      (\<forall>y. f y \<noteq> 0 \<longrightarrow> norm y \<le> R)
      \<longrightarrow>
      aim_complex_lp_on_plane (aim_hls_target_exponent a)
        (slp_partial_psi_inverse tau 0
          (slp_qstar_centered_square_denominator_source delta f)) \<and>
      aim_complex_lp_norm (aim_hls_target_exponent a)
          (slp_partial_psi_inverse tau 0
            (slp_qstar_centered_square_denominator_source delta f)) \<le>
        inverse pi * 4 *
          ((1 / delta) *
              integral\<^sup>L lborel (slp_localized_cauchy_kernel 1) *
              aim_complex_lp_norm (aim_hls_target_exponent a) f +
           C / ((a - 1) * (2 - a)) * (1 / delta) *
              slp_qstar_annular_J2_unit_coefficient_mass powr (1 / 2) *
              aim_complex_lp_norm (aim_hls_target_exponent a) f))"
proof -
  obtain C::real where C_positive: "0 < C"
    and raw_bound:
      "\<And>a delta R g.
        1 < a \<Longrightarrow> a < 2 \<Longrightarrow> 0 < delta \<Longrightarrow> delta \<le> R \<Longrightarrow>
        aim_complex_lp_on_plane (aim_hls_target_exponent a) g \<Longrightarrow>
        (\<And>y. g y \<noteq> 0 \<Longrightarrow> norm y \<le> R) \<Longrightarrow>
        aim_complex_lp_on_plane (aim_hls_target_exponent a)
            (slp_qstar_square_denominator_integral delta g) \<and>
        aim_complex_lp_norm (aim_hls_target_exponent a)
            (slp_qstar_square_denominator_integral delta g) \<le>
          4 *
            ((1 / delta) *
                integral\<^sup>L lborel (slp_localized_cauchy_kernel 1) *
                aim_complex_lp_norm (aim_hls_target_exponent a) g +
             C / ((a - 1) * (2 - a)) * (1 / delta) *
                slp_qstar_annular_J2_unit_coefficient_mass powr (1 / 2) *
                aim_complex_lp_norm (aim_hls_target_exponent a) g)"
    using slp_qstar_square_denominator_integral_complex_Lp by blast
  have all_outputs:
      "\<forall>a tau delta R f.
        1 < a \<and> a < 2 \<and> 0 < delta \<and> delta \<le> R \<and>
        aim_complex_lp_on_plane (aim_hls_target_exponent a) f \<and>
        (\<forall>y. f y \<noteq> 0 \<longrightarrow> norm y \<le> R)
      \<longrightarrow>
      aim_complex_lp_on_plane (aim_hls_target_exponent a)
        (slp_partial_psi_inverse tau 0
          (slp_qstar_centered_square_denominator_source delta f)) \<and>
      aim_complex_lp_norm (aim_hls_target_exponent a)
          (slp_partial_psi_inverse tau 0
            (slp_qstar_centered_square_denominator_source delta f)) \<le>
        inverse pi * 4 *
          ((1 / delta) *
              integral\<^sup>L lborel (slp_localized_cauchy_kernel 1) *
              aim_complex_lp_norm (aim_hls_target_exponent a) f +
           C / ((a - 1) * (2 - a)) * (1 / delta) *
              slp_qstar_annular_J2_unit_coefficient_mass powr (1 / 2) *
              aim_complex_lp_norm (aim_hls_target_exponent a) f)"
  proof (intro allI impI)
    fix a tau delta R :: real and f :: slp_scalar_field
    assume hypotheses:
      "1 < a \<and> a < 2 \<and> 0 < delta \<and> delta \<le> R \<and>
        aim_complex_lp_on_plane (aim_hls_target_exponent a) f \<and>
        (\<forall>y. f y \<noteq> 0 \<longrightarrow> norm y \<le> R)"
    have exponent_lower: "1 < a" and exponent_upper: "a < 2"
      and delta_positive: "0 < delta" and radius_lower: "delta \<le> R"
      and amplitude_lp:
        "aim_complex_lp_on_plane (aim_hls_target_exponent a) f"
      using hypotheses by blast+
    have amplitude_radius: "\<And>y. f y \<noteq> 0 \<Longrightarrow> norm y \<le> R"
      using hypotheses by blast
    let ?q = "aim_hls_target_exponent a"
    let ?g = "slp_oscillatory_modulation tau 0 f"
    let ?T = "slp_qstar_square_denominator_integral delta ?g"
    let ?S = "slp_partial_psi_inverse tau 0
      (slp_qstar_centered_square_denominator_source delta f)"
    let ?P = "(1 / delta) *
          integral\<^sup>L lborel (slp_localized_cauchy_kernel 1) *
          aim_complex_lp_norm ?q f +
       C / ((a - 1) * (2 - a)) * (1 / delta) *
          slp_qstar_annular_J2_unit_coefficient_mass powr (1 / 2) *
          aim_complex_lp_norm ?q f"
    let ?B = "4 * ?P"
    have q_above_two: "2 < ?q"
      by (rule slp_qstar_exponent_relations(1)[OF exponent_lower
            exponent_upper])
    have q_positive: "0 < ?q"
      using q_above_two by linarith
    have modulated_lp: "aim_complex_lp_on_plane ?q ?g"
      using amplitude_lp by simp
    have modulated_radius: "\<And>y. ?g y \<noteq> 0 \<Longrightarrow> norm y \<le> R"
    proof -
      fix y :: slp_point
      assume modulated_nonzero: "?g y \<noteq> 0"
      have amplitude_nonzero: "f y \<noteq> 0"
      proof
        assume "f y = 0"
        with modulated_nonzero show False
          unfolding slp_oscillatory_modulation_def by simp
      qed
      show "norm y \<le> R"
        by (rule amplitude_radius[OF amplitude_nonzero])
    qed
    have raw_data_modulated:
        "aim_complex_lp_on_plane ?q ?T \<and>
        aim_complex_lp_norm ?q ?T \<le>
          4 *
            ((1 / delta) *
                integral\<^sup>L lborel (slp_localized_cauchy_kernel 1) *
                aim_complex_lp_norm ?q ?g +
             C / ((a - 1) * (2 - a)) * (1 / delta) *
                slp_qstar_annular_J2_unit_coefficient_mass powr (1 / 2) *
                aim_complex_lp_norm ?q ?g)"
      by (rule raw_bound[OF exponent_lower exponent_upper delta_positive
            radius_lower modulated_lp modulated_radius])
    have raw_data:
        "aim_complex_lp_on_plane ?q ?T \<and>
        aim_complex_lp_norm ?q ?T \<le> ?B"
      using raw_data_modulated
      by (simp only: slp_oscillatory_modulation_lp_norm)
    have raw_lp: "aim_complex_lp_on_plane ?q ?T"
      using raw_data by blast
    have raw_norm: "aim_complex_lp_norm ?q ?T \<le> ?B"
      using raw_data by blast
    have coefficient_nonnegative: "0 \<le> inverse pi"
      by simp
    have constant_measurable:
        "(\<lambda>_::slp_point. inverse (of_real pi)) \<in>
          borel_measurable lborel"
      by measurable
    have constant_bound:
        "\<And>x::slp_point.
          norm (inverse (of_real pi) :: complex) \<le> inverse pi"
      by (simp only: norm_inverse norm_of_real abs_of_pos pi_gt_zero
            order_refl)
    have scaled_data:
        "aim_complex_lp_on_plane ?q
            (\<lambda>z. inverse (of_real pi) * ?T z) \<and>
        aim_complex_lp_norm ?q
            (\<lambda>z. inverse (of_real pi) * ?T z) \<le>
          inverse pi * aim_complex_lp_norm ?q ?T"
      using slp_complex_lp_bounded_multiplier[OF q_positive
          constant_measurable constant_bound coefficient_nonnegative raw_lp]
      by blast
    have output_eq:
        "?S = (\<lambda>z. inverse (of_real pi) * ?T z)"
      by (rule ext)
        (rule slp_qstar_centered_square_denominator_representation)
    have output_lp: "aim_complex_lp_on_plane ?q ?S"
      using scaled_data by (simp only: output_eq)
    have scaled_norm:
        "aim_complex_lp_norm ?q ?S \<le>
          inverse pi * aim_complex_lp_norm ?q ?T"
      using scaled_data by (simp only: output_eq)
    have propagated_bound:
        "inverse pi * aim_complex_lp_norm ?q ?T \<le> inverse pi * ?B"
      by (rule mult_left_mono[OF raw_norm coefficient_nonnegative])
    have output_bound:
        "aim_complex_lp_norm ?q ?S \<le> inverse pi * ?B"
      by (rule order_trans[OF scaled_norm propagated_bound])
    have output_bound_associated:
        "aim_complex_lp_norm ?q ?S \<le> inverse pi * 4 * ?P"
      using output_bound by (simp only: mult.assoc)
    show "aim_complex_lp_on_plane ?q ?S \<and>
        aim_complex_lp_norm ?q ?S \<le> inverse pi * 4 * ?P"
      using output_lp output_bound_associated by blast
  qed
  show ?thesis
    using C_positive all_outputs by blast
qed

end

end
