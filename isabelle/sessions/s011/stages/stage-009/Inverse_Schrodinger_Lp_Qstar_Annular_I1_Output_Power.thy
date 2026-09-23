theory Inverse_Schrodinger_Lp_Qstar_Annular_I1_Output_Power
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_009.Inverse_Schrodinger_Lp_Qstar_Annular_I1_Envelope"
    "HOL-Analysis.Ball_Volume"
begin

section \<open>Output power bound for the first annular term\<close>

theorem slp_qstar_annular_I1_output_power:
  assumes exponent_lower: "1 < a"
    and exponent_upper: "a < 2"
    and delta_positive: "0 < delta"
    and amplitude_lp:
      "aim_complex_lp_on_plane (aim_hls_target_exponent a) f"
  shows joint_measurable:
      "case_prod (slp_qstar_annular_I1_integrand delta f)
        \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    and potential_measurable:
      "slp_qstar_annular_I1_potential delta f
        \<in> borel_measurable lborel"
    and power_integrable:
      "integrable lborel
        (\<lambda>z. slp_qstar_annular_I1_potential delta f z powr
          aim_hls_target_exponent a)"
    and power_integral_bound:
      "integral\<^sup>L lborel
          (\<lambda>z. slp_qstar_annular_I1_potential delta f z powr
            aim_hls_target_exponent a) \<le>
        pi * (3 * delta) ^ 2 *
          ((1 / delta) *
            (delta powr (2 / slp_qstar_holder_exponent a - 1) *
              (integral\<^sup>L lborel
                (\<lambda>x. abs (slp_localized_cauchy_kernel 1 x) powr
                  slp_qstar_holder_exponent a))
                powr (1 / slp_qstar_holder_exponent a) *
              (integral\<^sup>L lborel
                (\<lambda>y. norm (f y) powr aim_hls_target_exponent a))
                powr (1 / aim_hls_target_exponent a)))
            powr aim_hls_target_exponent a"
proof -
  let ?q = "aim_hls_target_exponent a"
  let ?s = "slp_qstar_holder_exponent a"
  let ?K =
    "(integral\<^sup>L lborel
      (\<lambda>x. abs (slp_localized_cauchy_kernel 1 x) powr ?s))
      powr (1 / ?s)"
  let ?F =
    "(integral\<^sup>L lborel (\<lambda>y. norm (f y) powr ?q))
      powr (1 / ?q)"
  let ?M = "(1 / delta) * (delta powr (2 / ?s - 1) * ?K * ?F)"
  let ?ball = "cball (0 :: slp_point) (3 * delta)"
  have q_lower: "1 < ?q"
    using slp_qstar_exponent_relations(1)[OF exponent_lower exponent_upper]
    by linarith
  have q_positive: "0 < ?q"
    using q_lower by linarith
  have amplitude_measurable: "f \<in> borel_measurable lborel"
    using amplitude_lp unfolding aim_complex_lp_on_plane_def by blast
  have weighted_joint_measurable:
      "case_prod (slp_qstar_annular_I1_integrand delta f)
        \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    unfolding slp_qstar_annular_I1_integrand_def
      slp_annular_I1_integrand_def
    using amplitude_measurable by measurable
  show "case_prod (slp_qstar_annular_I1_integrand delta f)
      \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by (rule weighted_joint_measurable)
  have output_measurable:
      "slp_qstar_annular_I1_potential delta f
        \<in> borel_measurable lborel"
    unfolding slp_qstar_annular_I1_potential_def
    by (rule lborel.borel_measurable_lebesgue_integral[
          OF weighted_joint_measurable])
  show "slp_qstar_annular_I1_potential delta f
      \<in> borel_measurable lborel"
    by (rule output_measurable)
  have potential_nonnegative:
      "0 \<le> slp_qstar_annular_I1_potential delta f z" for z
    by (rule slp_qstar_annular_I1_envelope(3)[OF exponent_lower
          exponent_upper delta_positive amplitude_lp])
  have M_nonnegative: "0 \<le> ?M"
    by (intro mult_nonneg_nonneg)
      (use delta_positive in simp_all)
  have potential_le: "slp_qstar_annular_I1_potential delta f z \<le> ?M"
    for z
  proof -
    have envelope_bound:
        "slp_qstar_annular_I1_potential delta f z \<le>
          (1 / delta) * slp_localized_riesz_potential delta f z"
      by (rule slp_qstar_annular_I1_envelope(4)[OF exponent_lower
            exponent_upper delta_positive amplitude_lp])
    have holder_bound:
        "slp_localized_riesz_potential delta f z \<le>
          delta powr (2 / ?s - 1) * ?K * ?F"
      unfolding slp_localized_riesz_potential_def
      by (rule slp_qstar_localized_riesz_holder(2)[OF exponent_lower
            exponent_upper delta_positive amplitude_lp])
    have scaled_holder:
        "(1 / delta) * slp_localized_riesz_potential delta f z \<le> ?M"
      by (rule mult_left_mono[OF holder_bound])
        (use delta_positive in simp)
    show ?thesis
      using envelope_bound scaled_holder by linarith
  qed
  have power_measurable:
      "(\<lambda>z. slp_qstar_annular_I1_potential delta f z powr ?q)
        \<in> borel_measurable lborel"
    using output_measurable by measurable
  have ball_measurable: "?ball \<in> sets (lborel :: slp_point measure)"
    by measurable
  have ball_finite: "emeasure lborel ?ball < \<infinity>"
    by (rule emeasure_lborel_cball_finite)
  have indicator_integrable:
      "integrable lborel (indicator ?ball :: slp_point \<Rightarrow> real)"
    by (rule integrable_real_indicator[OF ball_measurable ball_finite])
  have majorant_integrable:
      "integrable lborel
        (\<lambda>z. (?M powr ?q) * indicator ?ball z)"
    using indicator_integrable by simp
  have power_pointwise:
      "slp_qstar_annular_I1_potential delta f z powr ?q \<le>
        (?M powr ?q) * indicator ?ball z" for z
  proof (cases "z \<in> ?ball")
    case True
    have powered:
        "slp_qstar_annular_I1_potential delta f z powr ?q \<le>
          ?M powr ?q"
      by (rule powr_mono2[OF less_imp_le[OF q_positive]
            potential_nonnegative potential_le])
    show ?thesis
      using powered True by simp
  next
    case False
    have potential_zero:
        "slp_qstar_annular_I1_potential delta f z = 0"
      by (rule slp_qstar_annular_I1_envelope(5)[OF exponent_lower
            exponent_upper delta_positive amplitude_lp False])
    show ?thesis
      using False potential_zero q_positive by simp
  qed
  have output_power_integrable:
      "integrable lborel
        (\<lambda>z. slp_qstar_annular_I1_potential delta f z powr ?q)"
  proof (rule Bochner_Integration.integrable_bound[
      OF majorant_integrable power_measurable])
    show "AE z in lborel.
        norm (slp_qstar_annular_I1_potential delta f z powr ?q) \<le>
          norm ((?M powr ?q) * indicator ?ball z)"
      using power_pointwise M_nonnegative by auto
  qed
  show "integrable lborel
      (\<lambda>z. slp_qstar_annular_I1_potential delta f z powr ?q)"
    by (rule output_power_integrable)
  have integral_le:
      "integral\<^sup>L lborel
          (\<lambda>z. slp_qstar_annular_I1_potential delta f z powr ?q) \<le>
        integral\<^sup>L lborel
          (\<lambda>z. (?M powr ?q) * indicator ?ball z)"
    by (rule Bochner_Integration.integral_mono[
          OF output_power_integrable majorant_integrable])
      (use power_pointwise in auto)
  have ball_measure:
      "measure lborel ?ball = pi * (3 * delta) ^ 2"
    using content_cball[where c="0 :: slp_point" and r="3 * delta"]
      delta_positive
    by (simp add: content_def unit_ball_vol_2)
  have majorant_integral:
      "integral\<^sup>L lborel
          (\<lambda>z. (?M powr ?q) * indicator ?ball z) =
        pi * (3 * delta) ^ 2 * (?M powr ?q)"
    using ball_measure by (simp add: mult.commute)
  show "integral\<^sup>L lborel
        (\<lambda>z. slp_qstar_annular_I1_potential delta f z powr ?q) \<le>
      pi * (3 * delta) ^ 2 * (?M powr ?q)"
    by (rule order_trans[OF integral_le])
      (simp only: majorant_integral)
qed

end
