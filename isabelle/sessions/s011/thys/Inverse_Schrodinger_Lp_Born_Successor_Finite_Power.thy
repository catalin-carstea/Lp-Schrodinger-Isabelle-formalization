theory Inverse_Schrodinger_Lp_Born_Successor_Finite_Power
  imports Inverse_Schrodinger_Lp_Born_Successor_Real_Bridge
begin

section \<open>Finite power is preserved by one positive Born successor\<close>

context aim_planar_riesz_hls
begin

lemma slp_positive_output_density_Suc_finite_power:
  fixes R C p a b L :: real
    and cutoff potential :: "slp_point \<Rightarrow> complex"
    and terminal_weight :: "slp_point \<Rightarrow> ennreal"
    and origin :: slp_point
    and n :: nat
  assumes radius_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and a_lower: "1 < a"
    and b_lower: "1 < b"
    and conjugate: "1 / a + 1 / b = 1"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and terminal_weight_measurable:
      "terminal_weight \<in> borel_measurable lborel"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and density_lp:
      "\<And>inner_origin. slp_positive_ennreal_lp_on_plane a
        (slp_positive_output_density R cutoff potential terminal_weight n
          inner_origin)"
    and density_power_bound:
      "\<And>inner_origin.
        integral\<^sup>L lborel
          (\<lambda>inner_output.
            enn2real
              (slp_positive_output_density R cutoff potential terminal_weight n
                inner_origin inner_output) powr a) \<le> L"
    and L_nonnegative: "0 \<le> L"
  shows successor_lp:
    "slp_positive_ennreal_lp_on_plane a
      (slp_positive_output_density R cutoff potential terminal_weight (Suc n)
        origin)"
    and successor_power_bound:
    "integral\<^sup>L lborel
        (\<lambda>output.
          enn2real
            (slp_positive_output_density R cutoff potential terminal_weight
              (Suc n) origin output) powr a) \<le>
      inverse (pi ^ 2) powr a *
        ((integral\<^sup>L lborel
            (slp_positive_branch_block_weight_real R cutoff potential origin))
            powr (a / b) *
          (L * integral\<^sup>L lborel
            (slp_positive_branch_block_weight_real R cutoff potential origin)))"
proof -
  let ?F =
    "slp_positive_output_density R cutoff potential terminal_weight (Suc n)
      origin"
  let ?weight =
    "slp_positive_branch_block_weight_real R cutoff potential origin"
  let ?datum =
    "slp_positive_branch_block_datum_real R cutoff potential terminal_weight n"
  let ?g =
    "\<lambda>output. integral\<^sup>L lborel
      (\<lambda>pair. ?weight pair * ?datum pair output)"
  let ?coefficient = "inverse (pi ^ 2)"
  have potential_measurable:
      "potential \<in> borel_measurable lborel"
    using potential_lp unfolding aim_complex_lp_on_plane_def by blast
  have F_measurable: "?F \<in> borel_measurable lborel"
    by (rule slp_positive_output_density_output_measurable[OF
          cutoff_measurable potential_measurable
            terminal_weight_measurable])
  have bridge:
      "AE output in lborel.
        ?F output = ennreal ?coefficient * ennreal (?g output)"
    by (rule slp_positive_output_density_Suc_real_bridge_AE[OF
          radius_nonnegative p_lower p_upper a_lower b_lower conjugate
          cutoff_measurable potential_lp terminal_weight_measurable
          cutoff_bound density_lp density_power_bound L_nonnegative])
  have target_integrable:
      "integrable lborel (\<lambda>output. ?g output powr a)"
    by (rule slp_positive_branch_block_real_finite_power(1)[OF
          radius_nonnegative p_lower p_upper a_lower b_lower conjugate
          cutoff_measurable potential_lp terminal_weight_measurable
          cutoff_bound density_lp density_power_bound L_nonnegative])
  have target_bound:
      "integral\<^sup>L lborel (\<lambda>output. ?g output powr a) \<le>
        (integral\<^sup>L lborel ?weight) powr (a / b) *
          (L * integral\<^sup>L lborel ?weight)"
    by (rule slp_positive_branch_block_real_finite_power(2)[OF
          radius_nonnegative p_lower p_upper a_lower b_lower conjugate
          cutoff_measurable potential_lp terminal_weight_measurable
          cutoff_bound density_lp density_power_bound L_nonnegative])
  have weight_nonnegative: "0 \<le> ?weight pair" for pair
    by (rule slp_positive_branch_block_weight_real_nonnegative)
  have datum_nonnegative: "0 \<le> ?datum pair out" for pair out
    by (rule slp_positive_branch_block_datum_real_nonnegative)
  have g_nonnegative: "0 \<le> ?g out" for out
    by (rule integral_nonneg_AE)
      (rule AE_I2, simp add: weight_nonnegative datum_nonnegative)
  have coefficient_positive: "0 < ?coefficient"
    by simp
  have coefficient_nonnegative: "0 \<le> ?coefficient"
    using coefficient_positive by simp
  have F_finite: "AE output in lborel. ?F output < top"
    using bridge
  proof eventually_elim
    fix out :: slp_point
    assume F_eq:
      "?F out = ennreal ?coefficient * ennreal (?g out)"
    show "?F out < top"
      unfolding F_eq by (simp add: ennreal_mult_less_top)
  qed
  have power_identity:
      "AE output in lborel.
        enn2real (?F output) powr a =
          (?coefficient powr a) * (?g output powr a)"
    using bridge
  proof eventually_elim
    fix out :: slp_point
    assume F_eq:
      "?F out = ennreal ?coefficient * ennreal (?g out)"
    show "enn2real (?F out) powr a =
        (?coefficient powr a) * (?g out powr a)"
      using coefficient_nonnegative g_nonnegative[of out]
      unfolding F_eq by (simp add: enn2real_mult powr_mult)
  qed
  have scaled_integrable:
      "integrable lborel
        (\<lambda>output. (?coefficient powr a) * (?g output powr a))"
    using target_integrable by simp
  have scaled_measurable:
      "(\<lambda>output. (?coefficient powr a) * (?g output powr a))
        \<in> borel_measurable lborel"
    using scaled_integrable borel_measurable_integrable by blast
  have F_power_measurable:
      "(\<lambda>output. enn2real (?F output) powr a)
        \<in> borel_measurable lborel"
    using F_measurable by measurable
  have F_power_integrable:
      "integrable lborel (\<lambda>output. enn2real (?F output) powr a)"
    by (rule integrable_cong_AE_imp[OF scaled_integrable F_power_measurable])
      (use power_identity in eventually_elim; simp)
  show successor_lp:
      "slp_positive_ennreal_lp_on_plane a ?F"
    unfolding slp_positive_ennreal_lp_on_plane_def
    using F_measurable F_finite F_power_integrable by blast
  have power_integral_identity:
      "integral\<^sup>L lborel
          (\<lambda>output. enn2real (?F output) powr a) =
        ?coefficient powr a *
          integral\<^sup>L lborel (\<lambda>output. ?g output powr a)"
  proof -
    have congruence:
        "integral\<^sup>L lborel
            (\<lambda>output. enn2real (?F output) powr a) =
          integral\<^sup>L lborel
            (\<lambda>output. ?coefficient powr a * (?g output powr a))"
      by (rule integral_cong_AE[OF
            F_power_measurable scaled_measurable power_identity])
    show ?thesis
      using congruence target_integrable by simp
  qed
  have scale_nonnegative: "0 \<le> ?coefficient powr a"
    by simp
  have scaled_bound:
      "?coefficient powr a *
          integral\<^sup>L lborel (\<lambda>output. ?g output powr a) \<le>
        ?coefficient powr a *
          ((integral\<^sup>L lborel ?weight) powr (a / b) *
            (L * integral\<^sup>L lborel ?weight))"
    by (rule mult_left_mono[OF target_bound scale_nonnegative])
  show successor_power_bound:
      "integral\<^sup>L lborel
          (\<lambda>output. enn2real (?F output) powr a) \<le>
        ?coefficient powr a *
          ((integral\<^sup>L lborel ?weight) powr (a / b) *
            (L * integral\<^sup>L lborel ?weight))"
    using power_integral_identity scaled_bound by simp
qed

end

end
