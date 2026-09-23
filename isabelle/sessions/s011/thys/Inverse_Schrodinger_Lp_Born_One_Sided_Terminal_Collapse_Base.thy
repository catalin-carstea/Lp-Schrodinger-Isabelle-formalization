theory Inverse_Schrodinger_Lp_Born_One_Sided_Terminal_Collapse_Base
  imports Inverse_Schrodinger_Lp_Born_One_Sided_Branch_Square_Recurrence
begin

section \<open>The one-block terminal collapse\<close>

definition slp_positive_terminal_riesz_weight ::
    "real \<Rightarrow> (slp_point \<Rightarrow> complex) \<Rightarrow>
      slp_point \<Rightarrow> ennreal"
where
  "slp_positive_terminal_riesz_weight R potential output =
    (\<integral>\<^sup>+source.
      ennreal (slp_localized_cauchy_kernel R (output - source)) *
        ennreal (norm (potential source)) \<partial>lborel)"

lemma slp_positive_terminal_riesz_weight_measurable:
  assumes potential_measurable[measurable]:
    "potential \<in> borel_measurable lborel"
  shows
    "slp_positive_terminal_riesz_weight R potential
      \<in> borel_measurable lborel"
  unfolding slp_positive_terminal_riesz_weight_def
  using slp_localized_cauchy_kernel_borel_measurable
  by measurable

theorem slp_positive_output_density_one_terminal_collapse:
  assumes cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and potential_measurable[measurable]:
      "potential \<in> borel_measurable lborel"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
  shows
    "slp_positive_output_density R cutoff potential (\<lambda>_. 1) 1
        origin output \<le>
      ennreal (inverse (pi ^ 2)) * ennreal C *
        (\<integral>\<^sup>+terminal.
          ennreal (slp_localized_cauchy_kernel R (terminal - output)) *
            slp_positive_output_density R cutoff potential
              (slp_positive_terminal_riesz_weight R potential) 0
              origin terminal
          \<partial>lborel)"
proof -
  note [measurable] = slp_localized_cauchy_kernel_borel_measurable
  let ?head = "\<lambda>pos_point.
    ennreal (slp_localized_cauchy_kernel R (origin - pos_point)) *
      ennreal (norm (cutoff pos_point))"
  let ?tail = "\<lambda>pos_point neg_point.
    ennreal (slp_localized_cauchy_kernel R (pos_point - neg_point)) *
      ennreal (norm (potential neg_point))"
  let ?beta = "slp_positive_terminal_riesz_weight R potential"
  let ?last_kernel = "\<lambda>pos_point.
    ennreal (slp_localized_cauchy_kernel R (pos_point - output))"
  let ?g = "\<lambda>pos_point.
    ?last_kernel pos_point *
      (ennreal (inverse pi) * ?head pos_point * ?beta pos_point)"
  have beta_measurable[measurable]:
      "?beta \<in> borel_measurable lborel"
    by (rule slp_positive_terminal_riesz_weight_measurable[OF
          potential_measurable])
  have tail_measurable:
      "(?tail pos_point) \<in> borel_measurable lborel"
    for pos_point
    by measurable
  have g_measurable: "?g \<in> borel_measurable lborel"
    by measurable
  have last_density_le:
      "slp_positive_output_density R cutoff potential (\<lambda>_. 1) 0
          neg_point (output - pos_point + neg_point) \<le>
        ennreal (inverse pi) * ?last_kernel pos_point * ennreal C"
    for pos_point neg_point
  proof -
    have cutoff_ennreal:
        "ennreal (norm (cutoff (output - pos_point + neg_point)))
          \<le> ennreal C"
      using cutoff_bound[of "output - pos_point + neg_point"] C_nonnegative
      by simp
    have kernel_identity:
        "slp_localized_cauchy_kernel R
            (neg_point - (output - pos_point + neg_point)) =
          slp_localized_cauchy_kernel R (pos_point - output)"
      by (simp add: algebra_simps)
    have scaled_cutoff:
        "(ennreal (inverse pi) * ?last_kernel pos_point) *
            ennreal (norm (cutoff (output - pos_point + neg_point))) \<le>
          (ennreal (inverse pi) * ?last_kernel pos_point) * ennreal C"
      by (rule mult_left_mono[OF cutoff_ennreal]) simp
    show ?thesis
      using scaled_cutoff
      by (simp add: slp_positive_output_density.simps kernel_identity
          mult.assoc)
  qed
  have inner_le:
      "(\<integral>\<^sup>+neg_point.
          ?head pos_point * ?tail pos_point neg_point *
            slp_positive_output_density R cutoff potential (\<lambda>_. 1) 0
              neg_point (output - pos_point + neg_point)
          \<partial>lborel) \<le>
        ennreal C * ?g pos_point"
    for pos_point
  proof -
    have integrand_le:
        "?head pos_point * ?tail pos_point neg_point *
              slp_positive_output_density R cutoff potential (\<lambda>_. 1) 0
                neg_point (output - pos_point + neg_point) \<le>
          (?head pos_point *
            (ennreal (inverse pi) * ?last_kernel pos_point * ennreal C)) *
            ?tail pos_point neg_point"
      for neg_point
    proof -
      have scaled:
          "(?head pos_point * ?tail pos_point neg_point) *
              slp_positive_output_density R cutoff potential (\<lambda>_. 1) 0
                neg_point (output - pos_point + neg_point) \<le>
            (?head pos_point * ?tail pos_point neg_point) *
              (ennreal (inverse pi) * ?last_kernel pos_point * ennreal C)"
        by (rule mult_left_mono[OF last_density_le]) simp
      show ?thesis
        using scaled
        by (simp add: mult.commute mult.left_commute mult.assoc)
    qed
    have monotone:
        "(\<integral>\<^sup>+neg_point.
            ?head pos_point * ?tail pos_point neg_point *
              slp_positive_output_density R cutoff potential (\<lambda>_. 1) 0
                neg_point (output - pos_point + neg_point)
            \<partial>lborel) \<le>
          (\<integral>\<^sup>+neg_point.
            (?head pos_point *
              (ennreal (inverse pi) * ?last_kernel pos_point * ennreal C)) *
              ?tail pos_point neg_point
            \<partial>lborel)"
      by (rule nn_integral_mono) (rule integrand_le)
    have extraction:
        "(\<integral>\<^sup>+neg_point.
            (?head pos_point *
              (ennreal (inverse pi) * ?last_kernel pos_point * ennreal C)) *
              ?tail pos_point neg_point
            \<partial>lborel) =
          (?head pos_point *
            (ennreal (inverse pi) * ?last_kernel pos_point * ennreal C)) *
            ?beta pos_point"
      unfolding slp_positive_terminal_riesz_weight_def
      by (rule nn_integral_cmult[OF tail_measurable])
    show ?thesis
      using monotone extraction
      by (simp add: mult.commute mult.left_commute mult.assoc)
  qed
  have outer_le:
      "(\<integral>\<^sup>+pos_point. \<integral>\<^sup>+neg_point.
          ?head pos_point * ?tail pos_point neg_point *
            slp_positive_output_density R cutoff potential (\<lambda>_. 1) 0
              neg_point (output - pos_point + neg_point)
          \<partial>lborel \<partial>lborel) \<le>
        ennreal C * (\<integral>\<^sup>+pos_point. ?g pos_point \<partial>lborel)"
  proof -
    have monotone:
        "(\<integral>\<^sup>+pos_point. \<integral>\<^sup>+neg_point.
            ?head pos_point * ?tail pos_point neg_point *
              slp_positive_output_density R cutoff potential (\<lambda>_. 1) 0
                neg_point (output - pos_point + neg_point)
            \<partial>lborel \<partial>lborel) \<le>
          (\<integral>\<^sup>+pos_point. ennreal C * ?g pos_point
            \<partial>lborel)"
      by (rule nn_integral_mono) (rule inner_le)
    show ?thesis
      using monotone nn_integral_cmult[OF g_measurable, of "ennreal C"]
      by simp
  qed
  have density_one:
      "slp_positive_output_density R cutoff potential (\<lambda>_. 1) 1
          origin output =
        ennreal (inverse (pi ^ 2)) *
          (\<integral>\<^sup>+pos_point. \<integral>\<^sup>+neg_point.
            ?head pos_point * ?tail pos_point neg_point *
              slp_positive_output_density R cutoff potential (\<lambda>_. 1) 0
                neg_point (output - pos_point + neg_point)
            \<partial>lborel \<partial>lborel)"
    by (simp add: mult.assoc)
  have target_integral:
      "(\<integral>\<^sup>+terminal.
          ennreal (slp_localized_cauchy_kernel R (terminal - output)) *
            slp_positive_output_density R cutoff potential ?beta 0
              origin terminal
          \<partial>lborel) =
        (\<integral>\<^sup>+terminal. ?g terminal \<partial>lborel)"
    by (rule nn_integral_cong) (simp add: mult.assoc)
  have scaled_outer:
      "ennreal (inverse (pi ^ 2)) *
          (\<integral>\<^sup>+pos_point. \<integral>\<^sup>+neg_point.
            ?head pos_point * ?tail pos_point neg_point *
              slp_positive_output_density R cutoff potential (\<lambda>_. 1) 0
                neg_point (output - pos_point + neg_point)
            \<partial>lborel \<partial>lborel) \<le>
        ennreal (inverse (pi ^ 2)) *
          (ennreal C * (\<integral>\<^sup>+pos_point. ?g pos_point \<partial>lborel))"
    by (rule mult_left_mono[OF outer_le]) simp
  show ?thesis
    using scaled_outer density_one target_integral
    by (simp add: mult.assoc)
qed

end
