theory Inverse_Schrodinger_Lp_Born_One_Sided_Step_Riesz
  imports Inverse_Schrodinger_Lp_Born_One_Sided_Zero_L2
begin

section \<open>Root extraction in the one-sided density recurrence\<close>

definition slp_positive_root_step_density ::
    "real \<Rightarrow> (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> ennreal) \<Rightarrow> nat \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow> slp_point \<Rightarrow> ennreal"
where
  "slp_positive_root_step_density R cutoff potential terminal_weight n
      root_weight output =
    ennreal (inverse (pi ^ 2)) *
      (\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
        ennreal (slp_localized_riesz_potential R root_weight pos_point) *
        ennreal (norm (cutoff pos_point)) *
        ennreal
          (slp_localized_cauchy_kernel R (pos_point - neg_point)) *
        ennreal (norm (potential neg_point)) *
        slp_positive_output_density R cutoff potential terminal_weight n
          neg_point (output - pos_point + neg_point)
        \<partial>lborel \<partial>lborel)"

lemma slp_localized_riesz_nn_integral:
  assumes root_integrable:
    "integrable lborel
      (slp_localized_riesz_integrand R root_weight output)"
  shows
    "(\<integral>\<^sup>+ root.
        ennreal (norm (root_weight root)) *
        ennreal (slp_localized_cauchy_kernel R (root - output))
        \<partial>lborel) =
      ennreal (slp_localized_riesz_potential R root_weight output)"
proof -
  let ?integrand = "slp_localized_riesz_integrand R root_weight output"
  have integrand_nonnegative: "AE root in lborel. 0 \<le> ?integrand root"
    by (rule AE_I2)
      (rule slp_localized_riesz_integrand_nonnegative)
  have positive_integral:
      "(\<integral>\<^sup>+ root. ennreal (?integrand root) \<partial>lborel) =
        ennreal (slp_localized_riesz_potential R root_weight output)"
    unfolding slp_localized_riesz_potential_def
    by (rule nn_integral_eq_integral[OF root_integrable
          integrand_nonnegative])
  have integrand_identity:
      "(\<lambda>root.
          ennreal (norm (root_weight root)) *
          ennreal (slp_localized_cauchy_kernel R (root - output))) =
        (\<lambda>root. ennreal (?integrand root))"
  proof (rule ext)
    fix root :: slp_point
    have kernel_nonnegative:
        "0 \<le> slp_localized_cauchy_kernel R (output - root)"
      by (rule slp_localized_cauchy_kernel_nonnegative)
    show "ennreal (norm (root_weight root)) *
          ennreal (slp_localized_cauchy_kernel R (root - output)) =
        ennreal (?integrand root)"
      unfolding slp_localized_riesz_integrand_def
      using kernel_nonnegative
      by (simp add: slp_localized_cauchy_kernel_reflect ennreal_mult
          mult.commute)
  qed
  show ?thesis
    using positive_integral by (simp only: integrand_identity)
qed

theorem slp_positive_root_output_density_Suc_riesz:
  assumes cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and potential_measurable[measurable]:
      "potential \<in> borel_measurable lborel"
    and terminal_weight_measurable[measurable]:
      "terminal_weight \<in> borel_measurable lborel"
    and root_weight_measurable[measurable]:
      "root_weight \<in> borel_measurable lborel"
    and root_fibers:
      "AE pos_point in lborel.
        integrable lborel
          (slp_localized_riesz_integrand R root_weight pos_point)"
  shows
    "slp_positive_root_output_density R cutoff potential terminal_weight
        (Suc n) root_weight output =
      slp_positive_root_step_density R cutoff potential terminal_weight n
        root_weight output"
proof -
  let ?root_kernel = "\<lambda>root pos_point.
    ennreal (norm (root_weight root)) *
      ennreal (slp_localized_cauchy_kernel R (root - pos_point))"
  let ?tail = "\<lambda>pos_point neg_point.
    ennreal (norm (cutoff pos_point)) *
      ennreal (slp_localized_cauchy_kernel R (pos_point - neg_point)) *
      ennreal (norm (potential neg_point)) *
      slp_positive_output_density R cutoff potential terminal_weight n
        neg_point (output - pos_point + neg_point)"
  let ?base = "\<lambda>root pos_point neg_point.
    ennreal (slp_localized_cauchy_kernel R (root - pos_point)) *
      ?tail pos_point neg_point"
  let ?joint = "\<lambda>root pos_point neg_point.
    ennreal (norm (root_weight root)) * ?base root pos_point neg_point"
  note [measurable] = slp_localized_cauchy_kernel_borel_measurable
    slp_positive_output_density_joint_measurable[OF cutoff_measurable
      potential_measurable terminal_weight_measurable]
  have root_pos_measurable:
      "case_prod (\<lambda>root pos_point.
          \<integral>\<^sup>+ neg_point. ?joint root pos_point neg_point
          \<partial>lborel) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by measurable
  have root_neg_measurable:
      "case_prod (\<lambda>root neg_point.
          ?joint root pos_point neg_point) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    for pos_point
    by measurable
  have root_kernel_measurable:
      "(\<lambda>root. ?root_kernel root pos_point) \<in>
        borel_measurable lborel"
    for pos_point
    by measurable
  have base_neg_measurable:
      "(\<lambda>neg_point. ?base root pos_point neg_point) \<in>
        borel_measurable lborel"
    for root pos_point
    by measurable
  have base_pos_integral_measurable:
      "(\<lambda>pos_point.
          \<integral>\<^sup>+ neg_point. ?base root pos_point neg_point
          \<partial>lborel) \<in> borel_measurable lborel"
    for root
    by measurable
  have density_suc:
      "slp_positive_output_density R cutoff potential terminal_weight
          (Suc n) root output =
        ennreal (inverse (pi ^ 2)) *
          (\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
            ?base root pos_point neg_point \<partial>lborel \<partial>lborel)"
    for root
    by (simp add: mult.commute mult.left_commute mult.assoc)
  have distribute_root_weight:
      "ennreal (norm (root_weight root)) *
          (\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
            ?base root pos_point neg_point \<partial>lborel \<partial>lborel) =
        (\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
          ?joint root pos_point neg_point \<partial>lborel \<partial>lborel)"
    for root
  proof -
    have inner:
        "(\<integral>\<^sup>+ neg_point. ?joint root pos_point neg_point
            \<partial>lborel) =
          ennreal (norm (root_weight root)) *
            (\<integral>\<^sup>+ neg_point. ?base root pos_point neg_point
              \<partial>lborel)"
      for pos_point
      by (rule nn_integral_cmult[OF base_neg_measurable])
    show ?thesis
      by (subst nn_integral_cmult[OF base_pos_integral_measurable,
            symmetric])
        (simp only: inner)
  qed
  have weighted_inner_measurable:
      "(\<lambda>root.
          ennreal (norm (root_weight root)) *
            (\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
              ?base root pos_point neg_point \<partial>lborel \<partial>lborel))
        \<in> borel_measurable lborel"
    by measurable
  have expanded:
      "slp_positive_root_output_density R cutoff potential terminal_weight
          (Suc n) root_weight output =
        ennreal (inverse (pi ^ 2)) *
          (\<integral>\<^sup>+ root. \<integral>\<^sup>+ pos_point.
            \<integral>\<^sup>+ neg_point. ?joint root pos_point neg_point
            \<partial>lborel \<partial>lborel \<partial>lborel)"
  proof -
    have coefficient_extract:
        "(\<integral>\<^sup>+ root.
            ennreal (norm (root_weight root)) *
              (ennreal (inverse (pi ^ 2)) *
                (\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
                  ?base root pos_point neg_point
                  \<partial>lborel \<partial>lborel))
            \<partial>lborel) =
          ennreal (inverse (pi ^ 2)) *
            (\<integral>\<^sup>+ root.
              ennreal (norm (root_weight root)) *
                (\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
                  ?base root pos_point neg_point
                  \<partial>lborel \<partial>lborel)
              \<partial>lborel)"
      by (simp only: mult.left_commute[of _ "ennreal (inverse (pi ^ 2))"]
            nn_integral_cmult[OF weighted_inner_measurable])
    show ?thesis
      unfolding slp_positive_root_output_density_def
      by (simp only: density_suc coefficient_extract
          distribute_root_weight)
  qed
  have swap_root_pos:
      "(\<integral>\<^sup>+ root. \<integral>\<^sup>+ pos_point.
          \<integral>\<^sup>+ neg_point. ?joint root pos_point neg_point
          \<partial>lborel \<partial>lborel \<partial>lborel) =
        (\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ root.
          \<integral>\<^sup>+ neg_point. ?joint root pos_point neg_point
          \<partial>lborel \<partial>lborel \<partial>lborel)"
    using lborel_pair.Fubini'[OF root_pos_measurable] by simp
  have swap_root_neg:
      "(\<integral>\<^sup>+ root. \<integral>\<^sup>+ neg_point.
          ?joint root pos_point neg_point \<partial>lborel \<partial>lborel) =
        (\<integral>\<^sup>+ neg_point. \<integral>\<^sup>+ root.
          ?joint root pos_point neg_point \<partial>lborel \<partial>lborel)"
    for pos_point
    using lborel_pair.Fubini'[OF root_neg_measurable] by simp
  have reorder:
      "(\<integral>\<^sup>+ root. \<integral>\<^sup>+ pos_point.
          \<integral>\<^sup>+ neg_point. ?joint root pos_point neg_point
          \<partial>lborel \<partial>lborel \<partial>lborel) =
        (\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
          \<integral>\<^sup>+ root. ?joint root pos_point neg_point
          \<partial>lborel \<partial>lborel \<partial>lborel)"
  proof -
    have inner:
        "(\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ root.
            \<integral>\<^sup>+ neg_point. ?joint root pos_point neg_point
            \<partial>lborel \<partial>lborel \<partial>lborel) =
          (\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
            \<integral>\<^sup>+ root. ?joint root pos_point neg_point
            \<partial>lborel \<partial>lborel \<partial>lborel)"
      by (rule nn_integral_cong)
        (rule swap_root_neg)
    show ?thesis
      using swap_root_pos inner by simp
  qed
  have factor_root:
      "(\<integral>\<^sup>+ root. ?joint root pos_point neg_point
          \<partial>lborel) =
        (\<integral>\<^sup>+ root. ?root_kernel root pos_point \<partial>lborel) *
          ?tail pos_point neg_point"
    for pos_point neg_point
  proof -
    have association:
        "(\<lambda>root. ?joint root pos_point neg_point) =
          (\<lambda>root.
            ?root_kernel root pos_point * ?tail pos_point neg_point)"
      by (rule ext) (simp add: mult.assoc)
    show ?thesis
      by (simp only: association
          nn_integral_multc[OF root_kernel_measurable])
  qed
  have root_replacement:
      "AE pos_point in lborel.
        (\<integral>\<^sup>+ neg_point.
          (\<integral>\<^sup>+ root. ?joint root pos_point neg_point
            \<partial>lborel) \<partial>lborel) =
        (\<integral>\<^sup>+ neg_point.
          ennreal (slp_localized_riesz_potential R root_weight pos_point) *
            ?tail pos_point neg_point
          \<partial>lborel)"
  proof (rule eventually_mono[OF root_fibers])
    fix pos_point :: slp_point
    assume fiber_integrable:
      "integrable lborel
        (slp_localized_riesz_integrand R root_weight pos_point)"
    have root_value:
        "(\<integral>\<^sup>+ root. ?root_kernel root pos_point \<partial>lborel) =
          ennreal (slp_localized_riesz_potential R root_weight pos_point)"
      by (rule slp_localized_riesz_nn_integral[OF fiber_integrable])
    show "(\<integral>\<^sup>+ neg_point.
          (\<integral>\<^sup>+ root. ?joint root pos_point neg_point
            \<partial>lborel) \<partial>lborel) =
        (\<integral>\<^sup>+ neg_point.
          ennreal (slp_localized_riesz_potential R root_weight pos_point) *
            ?tail pos_point neg_point
          \<partial>lborel)"
      by (simp only: factor_root root_value)
  qed
  have outer_replacement:
      "(\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
          \<integral>\<^sup>+ root. ?joint root pos_point neg_point
          \<partial>lborel \<partial>lborel \<partial>lborel) =
        (\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
          ennreal (slp_localized_riesz_potential R root_weight pos_point) *
            ?tail pos_point neg_point
          \<partial>lborel \<partial>lborel)"
    by (rule nn_integral_cong_AE[OF root_replacement])
  show ?thesis
    unfolding slp_positive_root_step_density_def
    using expanded reorder outer_replacement
    by (simp add: mult.assoc)
qed

end
