theory Inverse_Schrodinger_Lp_Born_Block_Mass_Endpoint
  imports
    Inverse_Schrodinger_Lp_Born_Block_Transport
    Inverse_Schrodinger_Lp_Born_Branch_Functional
    Inverse_Schrodinger_Lp_Double_Localized_Cauchy_Endpoint
begin

section \<open>Endpoint finiteness of one positive branch block\<close>

context aim_planar_riesz_hls
begin

theorem slp_positive_branch_block_mass_le_endpoint:
  fixes R C p :: real
    and cutoff potential :: "slp_point \<Rightarrow> complex"
    and origin :: slp_point
  assumes cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
  shows
    "(\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
        slp_positive_branch_block_weight R cutoff potential origin
          pos_point neg_point
        \<partial>lborel \<partial>lborel) \<le>
      ennreal C *
        (\<integral>\<^sup>+ neg_point.
          ennreal
            (slp_double_localized_cauchy_kernel R (origin - neg_point) *
              norm (potential neg_point))
          \<partial>lborel)"
proof -
  have potential_measurable[measurable]:
      "potential \<in> borel_measurable lborel"
    using potential_lp unfolding aim_complex_lp_on_plane_def by blast
  let ?kernel = "\<lambda>pos_point neg_point.
    ennreal (slp_localized_cauchy_kernel R (origin - pos_point)) *
    ennreal (slp_localized_cauchy_kernel R (pos_point - neg_point))"
  let ?outer = "\<lambda>neg_point.
    ennreal C * ennreal (norm (potential neg_point))"
  let ?major = "\<lambda>pos_point neg_point. ?outer neg_point * ?kernel pos_point neg_point"
  note [measurable] = slp_localized_cauchy_kernel_borel_measurable
  have major_joint:
      "case_prod ?major \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by measurable
  have kernel_slice[measurable]:
      "(\<lambda>pos_point. ?kernel pos_point neg_point) \<in>
        borel_measurable lborel"
    for neg_point
    by measurable
  have kernel_nonnegative:
      "0 \<le> slp_localized_cauchy_kernel R x"
    for x
    by (rule slp_localized_cauchy_kernel_nonnegative)
  have kernel_ennreal_product:
      "ennreal (slp_localized_cauchy_kernel R (origin - pos_point)) *
          ennreal
            (slp_localized_cauchy_kernel R (pos_point - neg_point)) =
        ennreal
          (slp_localized_cauchy_kernel R (origin - pos_point) *
            slp_localized_cauchy_kernel R (pos_point - neg_point))"
    for pos_point neg_point
    using kernel_nonnegative[of "origin - pos_point"]
      kernel_nonnegative[of "pos_point - neg_point"]
    by (simp add: ennreal_mult)
  have initial_bound_expanded:
      "(\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
          ennreal (slp_localized_cauchy_kernel R (origin - pos_point)) *
          ennreal (norm (cutoff pos_point)) *
          ennreal (slp_localized_cauchy_kernel R (pos_point - neg_point)) *
          ennreal (norm (potential neg_point))
          \<partial>(lborel :: slp_point measure)
          \<partial>(lborel :: slp_point measure)) \<le>
        (\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
          ?major pos_point neg_point
          \<partial>(lborel :: slp_point measure)
          \<partial>(lborel :: slp_point measure))"
  proof (rule nn_integral_mono_AE)
    show "AE pos_point in lborel.
      (\<integral>\<^sup>+ neg_point.
        ennreal (slp_localized_cauchy_kernel R (origin - pos_point)) *
        ennreal (norm (cutoff pos_point)) *
        ennreal (slp_localized_cauchy_kernel R (pos_point - neg_point)) *
        ennreal (norm (potential neg_point))
        \<partial>lborel) \<le>
      (\<integral>\<^sup>+ neg_point. ?major pos_point neg_point \<partial>lborel)"
    proof (rule AE_I2)
      fix pos_point :: slp_point
      show "(\<integral>\<^sup>+ neg_point.
          ennreal (slp_localized_cauchy_kernel R (origin - pos_point)) *
          ennreal (norm (cutoff pos_point)) *
          ennreal (slp_localized_cauchy_kernel R (pos_point - neg_point)) *
          ennreal (norm (potential neg_point))
          \<partial>lborel) \<le>
        (\<integral>\<^sup>+ neg_point. ?major pos_point neg_point \<partial>lborel)"
      proof (rule nn_integral_mono_AE)
        show "AE neg_point in lborel.
          ennreal (slp_localized_cauchy_kernel R (origin - pos_point)) *
          ennreal (norm (cutoff pos_point)) *
          ennreal (slp_localized_cauchy_kernel R (pos_point - neg_point)) *
          ennreal (norm (potential neg_point)) \<le>
            ?major pos_point neg_point"
        proof (rule AE_I2)
          fix neg_point :: slp_point
          have cutoff_ennreal:
              "ennreal (norm (cutoff pos_point)) \<le> ennreal C"
            by (rule ennreal_leI) (rule cutoff_bound)
          have cutoff_scaled:
              "ennreal (norm (cutoff pos_point)) *
                  (ennreal (norm (potential neg_point)) *
                    (ennreal
                        (slp_localized_cauchy_kernel R
                          (origin - pos_point)) *
                      ennreal
                        (slp_localized_cauchy_kernel R
                          (pos_point - neg_point)))) \<le>
                ennreal C *
                  (ennreal (norm (potential neg_point)) *
                    (ennreal
                        (slp_localized_cauchy_kernel R
                          (origin - pos_point)) *
                      ennreal
                        (slp_localized_cauchy_kernel R
                          (pos_point - neg_point))))"
            by (rule mult_right_mono[OF cutoff_ennreal]) simp
          show "ennreal
                (slp_localized_cauchy_kernel R (origin - pos_point)) *
              ennreal (norm (cutoff pos_point)) *
              ennreal
                (slp_localized_cauchy_kernel R (pos_point - neg_point)) *
              ennreal (norm (potential neg_point)) \<le>
              ?major pos_point neg_point"
            using cutoff_scaled by (simp add: mult_ac)
        qed
      qed
    qed
  qed
  have initial_bound:
      "(\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
          slp_positive_branch_block_weight R cutoff potential origin
            pos_point neg_point
          \<partial>lborel \<partial>lborel) \<le>
        (\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
          ?major pos_point neg_point
          \<partial>lborel \<partial>lborel)"
    using initial_bound_expanded
    unfolding slp_positive_branch_block_weight_def .
  have swap:
      "(\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
          ?major pos_point neg_point
          \<partial>lborel \<partial>lborel) =
        (\<integral>\<^sup>+ neg_point. \<integral>\<^sup>+ pos_point.
          ?major pos_point neg_point
          \<partial>lborel \<partial>lborel)"
    using lborel_pair.Fubini'[OF major_joint] by simp
  have factor_inner:
      "(\<integral>\<^sup>+ neg_point. \<integral>\<^sup>+ pos_point.
          ?major pos_point neg_point
          \<partial>lborel \<partial>lborel) =
        (\<integral>\<^sup>+ neg_point.
          ?outer neg_point *
            (\<integral>\<^sup>+ pos_point. ?kernel pos_point neg_point
              \<partial>lborel)
          \<partial>lborel)"
  proof -
    have inner_factor:
        "(\<integral>\<^sup>+ pos_point. ?major pos_point neg_point
            \<partial>lborel) =
          ?outer neg_point *
            (\<integral>\<^sup>+ pos_point. ?kernel pos_point neg_point
              \<partial>lborel)"
      for neg_point
      by (rule nn_integral_cmult[OF kernel_slice])
    show ?thesis
      by (simp only: inner_factor)
  qed
  have inner_AE:
      "AE neg_point in lborel.
        (\<integral>\<^sup>+ pos_point. ?kernel pos_point neg_point
          \<partial>lborel) =
        ennreal
          (slp_double_localized_cauchy_kernel R (origin - neg_point))"
    using slp_double_localized_cauchy_branch_inner_AE_nn_integral[
      of R origin]
    by eventually_elim (simp only: kernel_ennreal_product)
  have reduce_inner:
      "(\<integral>\<^sup>+ neg_point.
          ?outer neg_point *
            (\<integral>\<^sup>+ pos_point. ?kernel pos_point neg_point
              \<partial>lborel)
          \<partial>lborel) =
        (\<integral>\<^sup>+ neg_point.
          ?outer neg_point *
            ennreal
              (slp_double_localized_cauchy_kernel R (origin - neg_point))
          \<partial>lborel)"
  proof (rule nn_integral_cong_AE)
    show "AE neg_point in lborel.
        ?outer neg_point *
            (\<integral>\<^sup>+ pos_point. ?kernel pos_point neg_point
              \<partial>lborel) =
          ?outer neg_point *
            ennreal
              (slp_double_localized_cauchy_kernel R
                (origin - neg_point))"
      using inner_AE by eventually_elim simp
  qed
  have endpoint_form:
      "(\<integral>\<^sup>+ neg_point.
          ?outer neg_point *
            ennreal
              (slp_double_localized_cauchy_kernel R (origin - neg_point))
          \<partial>lborel) =
        ennreal C *
          (\<integral>\<^sup>+ neg_point.
            ennreal
              (slp_double_localized_cauchy_kernel R (origin - neg_point) *
                norm (potential neg_point))
            \<partial>lborel)"
  proof -
    have double_nonnegative:
        "0 \<le> slp_double_localized_cauchy_kernel R x"
      for x
      by (rule slp_double_localized_cauchy_kernel_nonnegative)
    have endpoint_product_measurable[measurable]:
        "(\<lambda>neg_point.
            ennreal (norm (potential neg_point)) *
              ennreal
                (slp_double_localized_cauchy_kernel R
                  (origin - neg_point))) \<in>
          borel_measurable lborel"
      using slp_double_localized_cauchy_kernel_borel_measurable
      by measurable
    have endpoint_product:
        "ennreal
            (slp_double_localized_cauchy_kernel R (origin - neg_point) *
              norm (potential neg_point)) =
          ennreal (norm (potential neg_point)) *
            ennreal
              (slp_double_localized_cauchy_kernel R
                (origin - neg_point))"
      for neg_point
      using double_nonnegative[of "origin - neg_point"]
      by (simp add: ennreal_mult mult.commute)
    have outer_extract:
        "(\<integral>\<^sup>+ neg_point.
            ennreal C *
              (ennreal (norm (potential neg_point)) *
                ennreal
                  (slp_double_localized_cauchy_kernel R
                    (origin - neg_point)))
            \<partial>lborel) =
          ennreal C *
            (\<integral>\<^sup>+ neg_point.
              ennreal (norm (potential neg_point)) *
                ennreal
                  (slp_double_localized_cauchy_kernel R
                    (origin - neg_point))
              \<partial>lborel)"
      by (rule nn_integral_cmult[OF endpoint_product_measurable])
    show ?thesis
      using outer_extract
      by (simp only: endpoint_product mult.assoc)
  qed
  show ?thesis
    using initial_bound swap factor_inner reduce_inner endpoint_form by simp
qed

theorem slp_positive_branch_block_mass_finite:
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
    "(\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
        slp_positive_branch_block_weight R cutoff potential origin
          pos_point neg_point
        \<partial>lborel \<partial>lborel) < \<infinity>"
proof -
  have mass_bound:
      "(\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
          slp_positive_branch_block_weight R cutoff potential origin
            pos_point neg_point
          \<partial>lborel \<partial>lborel) \<le>
        ennreal C *
          (\<integral>\<^sup>+ neg_point.
            ennreal
              (slp_double_localized_cauchy_kernel R (origin - neg_point) *
                norm (potential neg_point))
            \<partial>lborel)"
    by (rule slp_positive_branch_block_mass_le_endpoint[OF
          cutoff_measurable potential_lp cutoff_bound])
  have endpoint:
      "integrable lborel
        (slp_double_localized_endpoint_integrand R potential origin)"
    using slp_double_localized_cauchy_endpoint_bound[OF
      radius_nonnegative p_lower p_upper potential_lp]
    by blast
  have endpoint_nonnegative:
      "\<And>y. 0 \<le> slp_double_localized_endpoint_integrand R potential
        origin y"
    unfolding slp_double_localized_endpoint_integrand_def
    using slp_double_localized_cauchy_kernel_nonnegative[of R]
    by (simp add: mult_nonneg_nonneg)
  have endpoint_nonnegative_AE:
      "AE y in lborel.
        0 \<le> slp_double_localized_endpoint_integrand R potential origin y"
    by (rule AE_I2) (rule endpoint_nonnegative)
  have endpoint_nn_raw:
      "(\<integral>\<^sup>+ y.
          slp_double_localized_endpoint_integrand R potential origin y
          \<partial>lborel) =
        ennreal
          (integral\<^sup>L lborel
            (slp_double_localized_endpoint_integrand R potential origin))"
    by (rule nn_integral_eq_integral[OF endpoint endpoint_nonnegative_AE])
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
  have endpoint_finite:
      "ennreal C *
        (\<integral>\<^sup>+ y.
          ennreal
            (slp_double_localized_cauchy_kernel R (origin - y) *
              norm (potential y))
          \<partial>lborel) < \<infinity>"
    using endpoint_nn by (simp add: ennreal_mult_less_top)
  show ?thesis
    by (rule le_less_trans[OF mass_bound endpoint_finite])
qed

end

end
