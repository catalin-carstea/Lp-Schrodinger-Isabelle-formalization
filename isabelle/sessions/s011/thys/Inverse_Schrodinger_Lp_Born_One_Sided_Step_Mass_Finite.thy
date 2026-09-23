theory Inverse_Schrodinger_Lp_Born_One_Sided_Step_Mass_Finite
  imports Inverse_Schrodinger_Lp_Nonnegative_L2_Product
begin

section \<open>Finite concrete root-step mass\<close>

context aim_planar_riesz_hls
begin

theorem slp_positive_root_step_weight_mass_less_top:
  assumes radius_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
    and root_weight_lp: "aim_complex_lp_on_plane p root_weight"
    and root_weight_support: "bounded {x. root_weight x \<noteq> 0}"
  shows
    "(\<integral>\<^sup>+pos_point. \<integral>\<^sup>+neg_point.
      slp_positive_root_step_weight R cutoff root_weight root_weight
        pos_point neg_point \<partial>lborel \<partial>lborel) < top"
proof -
  let ?r = "slp_localized_riesz_potential R root_weight"
  have root_weight_measurable[measurable]:
      "root_weight \<in> borel_measurable lborel"
    using root_weight_lp unfolding aim_complex_lp_on_plane_def by blast
  have hls_data:
      "(AE z in lborel.
          integrable lborel
            (slp_localized_riesz_integrand R root_weight z)) \<and>
        aim_real_lp_on_plane 2 ?r \<and>
        bounded {z. ?r z \<noteq> 0}"
    by (rule slp_localized_riesz_l2_compact_lp[OF radius_nonnegative
          p_lower p_upper root_weight_lp root_weight_support])
  have fibers:
      "AE pos_point in lborel.
        integrable lborel
          (slp_localized_riesz_integrand R root_weight pos_point)"
    using hls_data by blast
  have r_l2: "aim_real_lp_on_plane 2 ?r"
    using hls_data by blast
  have r_nonnegative: "0 \<le> ?r x" for x
    by (rule slp_localized_riesz_potential_nonnegative)
  have r_measurable[measurable]: "?r \<in> borel_measurable lborel"
    using r_l2 unfolding aim_real_lp_on_plane_def by blast
  note [measurable] = slp_localized_cauchy_kernel_borel_measurable
  have inner_identity:
      "AE pos_point in lborel.
        (\<integral>\<^sup>+neg_point.
          slp_positive_root_step_weight R cutoff root_weight root_weight
            pos_point neg_point \<partial>lborel) =
        ennreal (?r pos_point) * ennreal (norm (cutoff pos_point)) *
          ennreal (?r pos_point)"
  proof (rule eventually_mono[OF fibers])
    fix pos_point
    assume fiber_integrable:
      "integrable lborel
        (slp_localized_riesz_integrand R root_weight pos_point)"
    have tail_measurable[measurable]:
        "(\<lambda>neg_point.
          ennreal
            (slp_localized_cauchy_kernel R (pos_point - neg_point)) *
          ennreal (norm (root_weight neg_point))) \<in>
        borel_measurable lborel"
      by measurable
    have scaled_tail_measurable[measurable]:
        "(\<lambda>neg_point.
          ennreal (norm (cutoff pos_point)) *
            (ennreal
              (slp_localized_cauchy_kernel R (pos_point - neg_point)) *
             ennreal (norm (root_weight neg_point)))) \<in>
        borel_measurable lborel"
      by measurable
    have slice:
        "(\<integral>\<^sup>+neg_point.
          ennreal
            (slp_localized_cauchy_kernel R (pos_point - neg_point)) *
          ennreal (norm (root_weight neg_point)) \<partial>lborel) =
        ennreal (?r pos_point)"
      using slp_localized_riesz_nn_integral[OF fiber_integrable]
      by (simp add: slp_localized_cauchy_kernel_reflect mult.commute)
    show
      "(\<integral>\<^sup>+neg_point.
          slp_positive_root_step_weight R cutoff root_weight root_weight
            pos_point neg_point \<partial>lborel) =
        ennreal (?r pos_point) * ennreal (norm (cutoff pos_point)) *
          ennreal (?r pos_point)"
      unfolding slp_positive_root_step_weight_def
      by (simp only: mult.assoc
          nn_integral_cmult[OF scaled_tail_measurable]
          nn_integral_cmult[OF tail_measurable] slice)
  qed
  have product_finite:
      "(\<integral>\<^sup>+x. ennreal (?r x) * ennreal (?r x)
          \<partial>lborel) < top"
    by (rule slp_nn_integral_product_lt_top_of_real_l2[OF r_l2 r_l2
          r_nonnegative r_nonnegative])
  have mass_bound:
      "(\<integral>\<^sup>+pos_point. \<integral>\<^sup>+neg_point.
          slp_positive_root_step_weight R cutoff root_weight root_weight
            pos_point neg_point \<partial>lborel \<partial>lborel) \<le>
        ennreal C *
          (\<integral>\<^sup>+pos_point.
            ennreal (?r pos_point) * ennreal (?r pos_point) \<partial>lborel)"
  proof -
    have pointwise:
        "ennreal (?r x) * ennreal (norm (cutoff x)) * ennreal (?r x) \<le>
          ennreal C * (ennreal (?r x) * ennreal (?r x))"
      for x
    proof -
      have cutoff_ennreal:
          "ennreal (norm (cutoff x)) \<le> ennreal C"
        by (rule ennreal_leI) (rule cutoff_bound)
      show ?thesis
        using cutoff_ennreal by (simp add: mult_ac mult_right_mono)
    qed
    have outer_le:
        "(\<integral>\<^sup>+pos_point.
          ennreal (?r pos_point) * ennreal (norm (cutoff pos_point)) *
            ennreal (?r pos_point) \<partial>lborel) \<le>
        (\<integral>\<^sup>+pos_point.
          ennreal C *
            (ennreal (?r pos_point) * ennreal (?r pos_point)) \<partial>lborel)"
      by (rule nn_integral_mono) (rule pointwise)
    have scaled:
        "(\<integral>\<^sup>+pos_point.
          ennreal C *
            (ennreal (?r pos_point) * ennreal (?r pos_point)) \<partial>lborel) =
        ennreal C *
          (\<integral>\<^sup>+pos_point.
            ennreal (?r pos_point) * ennreal (?r pos_point) \<partial>lborel)"
      by (rule nn_integral_cmult) measurable
    have mass_identity:
        "(\<integral>\<^sup>+pos_point. \<integral>\<^sup>+neg_point.
          slp_positive_root_step_weight R cutoff root_weight root_weight
            pos_point neg_point \<partial>lborel \<partial>lborel) =
        (\<integral>\<^sup>+pos_point.
          ennreal (?r pos_point) * ennreal (norm (cutoff pos_point)) *
            ennreal (?r pos_point) \<partial>lborel)"
      by (rule nn_integral_cong_AE) (rule inner_identity)
    show ?thesis
      using mass_identity outer_le scaled by simp
  qed
  show ?thesis
    by (rule le_less_trans[OF mass_bound])
      (simp add: ennreal_mult_less_top product_finite)
qed

end

end
