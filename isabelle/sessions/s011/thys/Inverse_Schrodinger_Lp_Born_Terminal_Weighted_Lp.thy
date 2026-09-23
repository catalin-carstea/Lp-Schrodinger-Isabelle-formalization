theory Inverse_Schrodinger_Lp_Born_Terminal_Weighted_Lp
  imports Inverse_Schrodinger_Lp_Born_All_Order_Weighted
begin

section \<open>The terminal Riesz weight at the manuscript exponent\<close>

lemma slp_positive_ennreal_lp_cong_AE:
  assumes F_measurable: "F \<in> borel_measurable lborel"
    and G_lp: "slp_positive_ennreal_lp_on_plane p G"
    and equality: "AE x in lborel. F x = G x"
  shows "slp_positive_ennreal_lp_on_plane p F"
proof -
  have G_components:
      "G \<in> borel_measurable lborel \<and>
        (AE x in lborel. G x < top_class.top) \<and>
        integrable lborel (\<lambda>x. enn2real (G x) powr p)"
    using G_lp by (simp only: slp_positive_ennreal_lp_on_plane_def)
  have G_finite: "AE x in lborel. G x < top_class.top"
    by (rule conjunct1[OF conjunct2[OF G_components]])
  have G_power_integrable:
      "integrable lborel (\<lambda>x. enn2real (G x) powr p)"
    by (rule conjunct2[OF conjunct2[OF G_components]])
  have F_finite: "AE x in lborel. F x < top_class.top"
    using equality G_finite
    by eventually_elim simp
  have F_power_measurable:
      "(\<lambda>x. enn2real (F x) powr p) \<in> borel_measurable lborel"
    using F_measurable by measurable
  have power_equality:
      "AE x in lborel.
        enn2real (G x) powr p = enn2real (F x) powr p"
    using equality by eventually_elim simp
  have F_power_integrable:
      "integrable lborel (\<lambda>x. enn2real (F x) powr p)"
    by (rule integrable_cong_AE_imp[OF G_power_integrable
          F_power_measurable power_equality])
  show ?thesis
    unfolding slp_positive_ennreal_lp_on_plane_def
    by (intro conjI; fact)
qed

context aim_planar_riesz_hls
begin

theorem slp_positive_terminal_riesz_weight_lp:
  assumes radius_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and potential_lp: "aim_complex_lp_on_plane p potential"
  shows
    "slp_positive_ennreal_lp_on_plane
      (slp_branch_terminal_exponent p)
      (slp_positive_terminal_riesz_weight R potential)"
proof -
  obtain C :: real where C_positive: "0 < C"
    and C_bound:
      "\<And>R p potential. 0 \<le> R \<Longrightarrow> 1 < p \<Longrightarrow> p < 2 \<Longrightarrow>
        aim_complex_lp_on_plane p potential \<Longrightarrow>
        (AE output in lborel.
          slp_positive_terminal_riesz_weight R potential output =
            ennreal (slp_localized_riesz_potential R potential output)) \<and>
        aim_real_lp_on_plane (aim_hls_target_exponent p)
          (slp_localized_riesz_potential R potential) \<and>
        aim_real_lp_norm (aim_hls_target_exponent p)
            (slp_localized_riesz_potential R potential)
          \<le> C / ((p - 1) * (2 - p)) * aim_complex_lp_norm p potential"
    using slp_positive_terminal_riesz_weight_hls by blast
  have hls_result:
      "(AE output in lborel.
          slp_positive_terminal_riesz_weight R potential output =
            ennreal (slp_localized_riesz_potential R potential output)) \<and>
        aim_real_lp_on_plane (aim_hls_target_exponent p)
          (slp_localized_riesz_potential R potential) \<and>
        aim_real_lp_norm (aim_hls_target_exponent p)
            (slp_localized_riesz_potential R potential)
          \<le> C / ((p - 1) * (2 - p)) * aim_complex_lp_norm p potential"
    by (rule C_bound[OF radius_nonnegative p_lower p_upper potential_lp])
  have terminal_identity:
      "AE output in lborel.
        slp_positive_terminal_riesz_weight R potential output =
          ennreal (slp_localized_riesz_potential R potential output)"
    using hls_result by blast
  have localized_lp:
      "aim_real_lp_on_plane (slp_branch_terminal_exponent p)
        (slp_localized_riesz_potential R potential)"
    using hls_result
    by (simp only: slp_branch_terminal_exponent_def
        aim_hls_target_exponent_def)
  have localized_nonnegative:
      "AE output in lborel.
        0 \<le> slp_localized_riesz_potential R potential output"
    by (rule AE_I2) (rule slp_localized_riesz_potential_nonnegative)
  have lifted_lp:
      "slp_positive_ennreal_lp_on_plane
        (slp_branch_terminal_exponent p)
        (\<lambda>output.
          ennreal (slp_localized_riesz_potential R potential output))"
    by (rule slp_positive_ennreal_lp_from_real[OF localized_lp
          localized_nonnegative])
  have potential_measurable:
      "potential \<in> borel_measurable lborel"
    using potential_lp unfolding aim_complex_lp_on_plane_def by blast
  have terminal_measurable:
      "slp_positive_terminal_riesz_weight R potential
        \<in> borel_measurable lborel"
    by (rule slp_positive_terminal_riesz_weight_measurable[OF
          potential_measurable])
  show ?thesis
    by (rule slp_positive_ennreal_lp_cong_AE[OF terminal_measurable
          lifted_lp terminal_identity])
qed

end

end
