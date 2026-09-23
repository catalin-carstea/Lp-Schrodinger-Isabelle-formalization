theory Inverse_Schrodinger_Lp_Born_Block_Real_Integrable
  imports Inverse_Schrodinger_Lp_Born_Block_Real_Representatives
begin

section \<open>Integrability of the exact real Born-block data\<close>

context aim_planar_riesz_hls
begin

lemma slp_positive_branch_block_weight_real_integrable:
  fixes R C p :: real
    and cutoff potential :: "slp_point \<Rightarrow> complex"
    and origin :: slp_point
  assumes radius_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
  shows
    "integrable lborel
      (slp_positive_branch_block_weight_real R cutoff potential origin)"
proof -
  have locale_instance: "aim_planar_riesz_hls"
    by unfold_locales (rule aim_planar_riesz_hls)
  have potential_measurable:
      "potential \<in> borel_measurable lborel"
    using potential_lp unfolding aim_complex_lp_on_plane_def by blast
  have block_measurable:
      "case_prod
          (slp_positive_branch_block_weight R cutoff potential origin)
        \<in> borel_measurable
          ((lborel :: slp_point measure) \<Otimes>\<^sub>M
            (lborel :: slp_point measure))"
    by (rule slp_positive_branch_block_weight_measurable[OF
          cutoff_measurable potential_measurable])
  have nested_finite:
      "(\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
          slp_positive_branch_block_weight R cutoff potential origin
            pos_point neg_point
          \<partial>lborel \<partial>lborel) < \<infinity>"
    by (rule aim_planar_riesz_hls.slp_positive_branch_block_mass_finite[
          where R=R and C=C and p=p and cutoff=cutoff and
            potential=potential and origin=origin, OF
          locale_instance])
      (use radius_nonnegative p_lower p_upper cutoff_measurable
        potential_lp cutoff_bound in auto)
  have product_finite:
      "integral\<^sup>N
          ((lborel :: slp_point measure) \<Otimes>\<^sub>M
            (lborel :: slp_point measure))
          (case_prod
            (slp_positive_branch_block_weight R cutoff potential origin))
        < top"
    using nested_finite
      lborel.nn_integral_fst[OF block_measurable] by simp
  have exact_pair_finite:
      "(\<integral>\<^sup>+ pair.
          case_prod
            (slp_positive_branch_block_weight R cutoff potential origin)
            pair
          \<partial>(lborel :: (slp_point \<times> slp_point) measure)) < top"
    using product_finite by (simp only: lborel_prod)
  have weight_nn_integral:
      "(\<integral>\<^sup>+ pair.
          slp_positive_branch_block_weight_real R cutoff potential origin pair
          \<partial>lborel) =
        (\<integral>\<^sup>+ pair.
          case_prod
            (slp_positive_branch_block_weight R cutoff potential origin)
            pair
          \<partial>lborel)"
  proof (rule nn_integral_cong)
    fix pair :: "slp_point \<times> slp_point"
    show
      "ennreal
          (slp_positive_branch_block_weight_real R cutoff potential origin
            pair) =
        case_prod
          (slp_positive_branch_block_weight R cutoff potential origin) pair"
      using slp_positive_branch_block_weight_real_lift[of
        R cutoff potential origin pair]
      by (cases pair) simp
  qed
  have weight_nn_finite:
      "(\<integral>\<^sup>+ pair.
          slp_positive_branch_block_weight_real R cutoff potential origin pair
          \<partial>lborel) < top"
    using exact_pair_finite weight_nn_integral by simp
  show ?thesis
  proof (rule integrableI_nonneg)
    show
      "slp_positive_branch_block_weight_real R cutoff potential origin
        \<in> borel_measurable lborel"
      by (rule slp_positive_branch_block_weight_real_measurable[OF
            cutoff_measurable potential_measurable])
    show
      "AE pair in lborel.
        0 \<le> slp_positive_branch_block_weight_real R cutoff potential origin
          pair"
      by (rule AE_I2)
        (rule slp_positive_branch_block_weight_real_nonnegative)
    show
      "(\<integral>\<^sup>+ pair.
          slp_positive_branch_block_weight_real R cutoff potential origin pair
          \<partial>lborel) < \<infinity>"
      using weight_nn_finite by simp
  qed
qed

end

lemma slp_positive_branch_block_datum_real_power_integrable:
  assumes density_lp:
    "\<And>origin. slp_positive_ennreal_lp_on_plane a
      (slp_positive_output_density R cutoff potential terminal_weight n
        origin)"
  shows
    "integrable lborel
      (\<lambda>output.
        slp_positive_branch_block_datum_real R cutoff potential
          terminal_weight n pair output powr a)"
proof -
  have inner_power_integrable:
      "integrable lborel
        (\<lambda>inner_output.
          enn2real
            (slp_positive_output_density R cutoff potential terminal_weight n
              (snd pair) inner_output) powr a)"
    using density_lp[of "snd pair"]
    unfolding slp_positive_ennreal_lp_on_plane_def by blast
  have translated_power_integrable:
      "integrable lborel
        (\<lambda>output.
          enn2real
            (slp_positive_output_density R cutoff potential terminal_weight n
              (snd pair) ((- fst pair + snd pair) + output)) powr a)"
    by (rule slp_lborel_integrable_translate[OF inner_power_integrable])
  show ?thesis
    using translated_power_integrable
    unfolding slp_positive_branch_block_datum_real_def
    by (simp add: algebra_simps)
qed

end
