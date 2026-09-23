theory Inverse_Schrodinger_Lp_Qstar_Centered_Cutoff_Partial_Complex_Lp
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_010.Inverse_Schrodinger_Lp_Qstar_Centered_Annular_Representation"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_010.Inverse_Schrodinger_Lp_Complex_Lp_Bounded_Multiplier"
begin

section \<open>Centered cutoff-derivative partial-Cauchy Lp bound\<close>

context aim_planar_riesz_hls
begin

theorem slp_qstar_centered_cutoff_partial_source_complex_Lp:
  "\<exists>C::real. 0 < C \<and>
    (\<forall>a tau delta f. 1 < a \<and> a < 2 \<and> 0 < delta \<and>
        aim_complex_lp_on_plane (aim_hls_target_exponent a) f
      \<longrightarrow>
      aim_complex_lp_on_plane (aim_hls_target_exponent a)
        (slp_partial_psi_inverse tau 0
          (slp_qstar_centered_cutoff_partial_source delta f)) \<and>
      aim_complex_lp_norm (aim_hls_target_exponent a)
          (slp_partial_psi_inverse tau 0
            (slp_qstar_centered_cutoff_partial_source delta f)) \<le>
        inverse pi *
          ((slp_global_cutoff_L / delta) * 4 *
            ((9 * pi) powr (1 / aim_hls_target_exponent a) *
              (integral\<^sup>L lborel
                (\<lambda>x. abs (slp_localized_cauchy_kernel 1 x) powr
                  slp_qstar_holder_exponent a))
                powr (1 / slp_qstar_holder_exponent a) *
              aim_complex_lp_norm (aim_hls_target_exponent a) f +
             C / ((a - 1) * (2 - a)) *
              (integral\<^sup>L lborel
                (slp_squared_radial_annulus 1 2)) powr (1 / 2) *
              aim_complex_lp_norm (aim_hls_target_exponent a) f)))"
proof -
  obtain C::real where C_positive: "0 < C"
    and raw_bound:
      "\<And>a delta g. 1 < a \<Longrightarrow> a < 2 \<Longrightarrow> 0 < delta \<Longrightarrow>
        aim_complex_lp_on_plane (aim_hls_target_exponent a) g \<Longrightarrow>
        aim_complex_lp_on_plane (aim_hls_target_exponent a)
            (slp_qstar_cutoff_partial_integral delta g) \<and>
        aim_complex_lp_norm (aim_hls_target_exponent a)
            (slp_qstar_cutoff_partial_integral delta g) \<le>
          (slp_global_cutoff_L / delta) * 4 *
            ((9 * pi) powr (1 / aim_hls_target_exponent a) *
              (integral\<^sup>L lborel
                (\<lambda>x. abs (slp_localized_cauchy_kernel 1 x) powr
                  slp_qstar_holder_exponent a))
                powr (1 / slp_qstar_holder_exponent a) *
              aim_complex_lp_norm (aim_hls_target_exponent a) g +
             C / ((a - 1) * (2 - a)) *
              (integral\<^sup>L lborel
                (slp_squared_radial_annulus 1 2)) powr (1 / 2) *
              aim_complex_lp_norm (aim_hls_target_exponent a) g)"
    using slp_qstar_cutoff_partial_integral_complex_Lp by blast
  have all_outputs:
      "\<forall>a tau delta f. 1 < a \<and> a < 2 \<and> 0 < delta \<and>
        aim_complex_lp_on_plane (aim_hls_target_exponent a) f
      \<longrightarrow>
      aim_complex_lp_on_plane (aim_hls_target_exponent a)
        (slp_partial_psi_inverse tau 0
          (slp_qstar_centered_cutoff_partial_source delta f)) \<and>
      aim_complex_lp_norm (aim_hls_target_exponent a)
          (slp_partial_psi_inverse tau 0
            (slp_qstar_centered_cutoff_partial_source delta f)) \<le>
        inverse pi *
          ((slp_global_cutoff_L / delta) * 4 *
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
  proof (intro allI impI)
    fix a tau delta :: real and f :: slp_scalar_field
    assume hypotheses:
      "1 < a \<and> a < 2 \<and> 0 < delta \<and>
        aim_complex_lp_on_plane (aim_hls_target_exponent a) f"
    have exponent_lower: "1 < a" and exponent_upper: "a < 2"
      and delta_positive: "0 < delta"
      and amplitude_lp:
        "aim_complex_lp_on_plane (aim_hls_target_exponent a) f"
      using hypotheses by blast+
    let ?q = "aim_hls_target_exponent a"
    let ?g = "slp_oscillatory_modulation tau 0 f"
    let ?T = "slp_qstar_cutoff_partial_integral delta ?g"
    let ?S = "slp_partial_psi_inverse tau 0
      (slp_qstar_centered_cutoff_partial_source delta f)"
    let ?B = "(slp_global_cutoff_L / delta) * 4 *
      ((9 * pi) powr (1 / ?q) *
        (integral\<^sup>L lborel
          (\<lambda>x. abs (slp_localized_cauchy_kernel 1 x) powr
            slp_qstar_holder_exponent a))
          powr (1 / slp_qstar_holder_exponent a) *
        aim_complex_lp_norm ?q f +
       C / ((a - 1) * (2 - a)) *
        (integral\<^sup>L lborel
          (slp_squared_radial_annulus 1 2)) powr (1 / 2) *
        aim_complex_lp_norm ?q f)"
    have q_above_two: "2 < ?q"
      by (rule slp_qstar_exponent_relations(1)[OF exponent_lower
            exponent_upper])
    have q_positive: "0 < ?q"
      using q_above_two by linarith
    have modulated_lp: "aim_complex_lp_on_plane ?q ?g"
      using amplitude_lp by simp
    have raw_data:
        "aim_complex_lp_on_plane ?q ?T \<and>
        aim_complex_lp_norm ?q ?T \<le> ?B"
      using raw_bound[OF exponent_lower exponent_upper delta_positive
          modulated_lp]
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
        (rule slp_qstar_centered_cutoff_partial_representation)
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
    show "aim_complex_lp_on_plane ?q ?S \<and>
        aim_complex_lp_norm ?q ?S \<le> inverse pi * ?B"
      using output_lp output_bound by blast
  qed
  show ?thesis
    using C_positive all_outputs by blast
qed

end

end
