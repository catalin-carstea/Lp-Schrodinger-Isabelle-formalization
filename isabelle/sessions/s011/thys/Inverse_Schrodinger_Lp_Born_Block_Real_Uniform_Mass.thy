theory Inverse_Schrodinger_Lp_Born_Block_Real_Uniform_Mass
  imports
    Inverse_Schrodinger_Lp_Born_Successor_Finite_Power
    Inverse_Schrodinger_Lp_Born_Block_Uniform_Mass
begin

section \<open>Origin-uniform real Born-block mass\<close>

context aim_planar_riesz_hls
begin

lemma slp_positive_branch_block_weight_real_uniform:
  fixes R C p :: real
    and cutoff potential :: "slp_point \<Rightarrow> complex"
  assumes radius_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
  shows
    "\<exists>B. 0 \<le> B \<and>
      (\<forall>origin.
        integral\<^sup>L lborel
          (slp_positive_branch_block_weight_real R cutoff potential origin)
          \<le> B)"
proof -
  obtain E where E_finite: "E < top"
    and extended_uniform:
      "\<forall>origin.
        (\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
          slp_positive_branch_block_weight R cutoff potential origin
            pos_point neg_point
          \<partial>lborel \<partial>lborel) \<le> E"
    using slp_positive_branch_block_mass_uniform[OF
      radius_nonnegative p_lower p_upper cutoff_measurable potential_lp
      cutoff_bound C_nonnegative] by blast
  let ?B = "enn2real E"
  have B_nonnegative: "0 \<le> ?B"
    by simp
  have real_uniform:
      "integral\<^sup>L lborel
          (slp_positive_branch_block_weight_real R cutoff potential origin)
        \<le> ?B"
    for origin
  proof -
    let ?real_weight =
      "slp_positive_branch_block_weight_real R cutoff potential origin"
    let ?extended_weight =
      "slp_positive_branch_block_weight R cutoff potential origin"
    have potential_measurable:
        "potential \<in> borel_measurable lborel"
      using potential_lp unfolding aim_complex_lp_on_plane_def by blast
    have real_integrable: "integrable lborel ?real_weight"
      by (rule slp_positive_branch_block_weight_real_integrable[OF
            radius_nonnegative p_lower p_upper cutoff_measurable
            potential_lp cutoff_bound])
    have real_nonnegative: "0 \<le> ?real_weight pair" for pair
      by (rule slp_positive_branch_block_weight_real_nonnegative)
    have real_integral_nonnegative:
        "0 \<le> integral\<^sup>L lborel ?real_weight"
      by (rule integral_nonneg_AE)
        (rule AE_I2, rule real_nonnegative)
    have real_nn:
        "(\<integral>\<^sup>+ pair. ennreal (?real_weight pair) \<partial>lborel) =
          ennreal (integral\<^sup>L lborel ?real_weight)"
      by (rule nn_integral_eq_integral[OF real_integrable])
        (rule AE_I2, rule real_nonnegative)
    have lift_nn:
        "(\<integral>\<^sup>+ pair. ennreal (?real_weight pair) \<partial>lborel) =
          (\<integral>\<^sup>+ pair. case_prod ?extended_weight pair
            \<partial>(lborel :: (slp_point \<times> slp_point) measure))"
    proof (rule nn_integral_cong)
      fix pair :: "slp_point \<times> slp_point"
      show "ennreal (?real_weight pair) = case_prod ?extended_weight pair"
        using slp_positive_branch_block_weight_real_lift[of
          R cutoff potential origin pair]
        by (cases pair) simp
    qed
    have block_measurable:
        "case_prod ?extended_weight \<in> borel_measurable
          ((lborel :: slp_point measure) \<Otimes>\<^sub>M
            (lborel :: slp_point measure))"
      by (rule slp_positive_branch_block_weight_measurable[OF
            cutoff_measurable potential_measurable])
    have product_nested:
        "(\<integral>\<^sup>+ pair. case_prod ?extended_weight pair
            \<partial>(lborel :: (slp_point \<times> slp_point) measure)) =
          (\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
            ?extended_weight pos_point neg_point
            \<partial>lborel \<partial>lborel)"
    proof -
      have fubini:
          "(\<integral>\<^sup>+ pair. case_prod ?extended_weight pair
              \<partial>((lborel :: slp_point measure) \<Otimes>\<^sub>M
                (lborel :: slp_point measure))) =
            (\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
              ?extended_weight pos_point neg_point
              \<partial>lborel \<partial>lborel)"
        using lborel.nn_integral_fst[OF block_measurable] by simp
      show ?thesis
        using fubini by (simp only: lborel_prod)
    qed
    have lifted_le: "ennreal (integral\<^sup>L lborel ?real_weight) \<le> E"
      using extended_uniform[rule_format, of origin]
        real_nn lift_nn product_nested by simp
    have converted_le:
        "enn2real (ennreal (integral\<^sup>L lborel ?real_weight)) \<le> ?B"
      by (rule enn2real_mono[OF lifted_le E_finite])
    show ?thesis
      using converted_le real_integral_nonnegative by simp
  qed
  show ?thesis
    by (intro exI[of _ ?B] conjI B_nonnegative allI real_uniform)
qed

end

end
