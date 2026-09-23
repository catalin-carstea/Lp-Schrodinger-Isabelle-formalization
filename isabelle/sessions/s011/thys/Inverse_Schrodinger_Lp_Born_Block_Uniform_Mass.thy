theory Inverse_Schrodinger_Lp_Born_Block_Uniform_Mass
  imports Inverse_Schrodinger_Lp_Born_Block_Mass_Endpoint
begin

section \<open>Origin-uniform endpoint block mass\<close>

context aim_planar_riesz_hls
begin

theorem slp_positive_branch_block_mass_uniform:
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
    "\<exists>B. B < top \<and>
      (\<forall>origin.
        (\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
          slp_positive_branch_block_weight R cutoff potential origin
            pos_point neg_point
          \<partial>lborel \<partial>lborel) \<le> B)"
proof -
  let ?q = "slp_holder_conjugate p"
  let ?A =
    "integral\<^sup>L lborel
        (\<lambda>x. abs (slp_double_localized_cauchy_kernel R x) powr ?q) / ?q +
      integral\<^sup>L lborel (\<lambda>y. norm (potential y) powr p) / p"
  let ?B = "ennreal C * ennreal ?A"
  have endpoint_data:
      "\<forall>origin.
        integrable lborel
          (slp_double_localized_endpoint_integrand R potential origin) \<and>
        slp_double_localized_endpoint_potential R potential origin \<le> ?A"
    by (rule slp_double_localized_cauchy_endpoint_bound[OF
          radius_nonnegative p_lower p_upper potential_lp])
  have B_finite: "?B < top"
    by (simp add: ennreal_mult_less_top)
  have uniform_bound:
      "(\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
          slp_positive_branch_block_weight R cutoff potential origin
            pos_point neg_point
          \<partial>lborel \<partial>lborel) \<le> ?B"
    for origin
  proof -
    have endpoint_integrable:
        "integrable lborel
          (slp_double_localized_endpoint_integrand R potential origin)"
      using endpoint_data by blast
    have endpoint_le:
        "slp_double_localized_endpoint_potential R potential origin \<le> ?A"
      using endpoint_data by blast
    have endpoint_nonnegative_AE:
        "AE y in lborel.
          0 \<le>
            slp_double_localized_endpoint_integrand R potential origin y"
      unfolding slp_double_localized_endpoint_integrand_def
      by (rule AE_I2)
        (simp add: slp_double_localized_cauchy_kernel_nonnegative)
    have endpoint_nn_raw:
        "(\<integral>\<^sup>+ y.
            slp_double_localized_endpoint_integrand R potential origin y
            \<partial>lborel) =
          ennreal
            (integral\<^sup>L lborel
              (slp_double_localized_endpoint_integrand R potential origin))"
      by (rule nn_integral_eq_integral[OF endpoint_integrable
            endpoint_nonnegative_AE])
    have endpoint_nn:
        "(\<integral>\<^sup>+ y.
            ennreal
              (slp_double_localized_cauchy_kernel R (origin - y) *
                norm (potential y))
            \<partial>lborel) =
          ennreal
            (slp_double_localized_endpoint_potential R potential origin)"
      using endpoint_nn_raw
      unfolding slp_double_localized_endpoint_integrand_def
        slp_double_localized_endpoint_potential_def .
    have mass_bound:
        "(\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
            slp_positive_branch_block_weight R cutoff potential origin
              pos_point neg_point
            \<partial>lborel \<partial>lborel) \<le>
          ennreal C *
            (\<integral>\<^sup>+ neg_point.
              ennreal
                (slp_double_localized_cauchy_kernel R
                    (origin - neg_point) *
                  norm (potential neg_point))
              \<partial>lborel)"
      by (rule slp_positive_branch_block_mass_le_endpoint[OF
            cutoff_measurable potential_lp cutoff_bound])
    have endpoint_ennreal_le:
        "ennreal
            (slp_double_localized_endpoint_potential R potential origin) \<le>
          ennreal ?A"
      by (rule ennreal_leI) (rule endpoint_le)
    have scaled_endpoint:
        "ennreal C *
            ennreal
              (slp_double_localized_endpoint_potential R potential origin) \<le>
          ?B"
      by (rule mult_left_mono[OF endpoint_ennreal_le]) simp
    show ?thesis
      using mass_bound endpoint_nn scaled_endpoint by simp
  qed
  show ?thesis
    by (intro exI[of _ ?B] conjI B_finite allI uniform_bound)
qed

end

end
