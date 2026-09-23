theory Inverse_Schrodinger_Lp_Born_One_Sided_Terminal_Collapse
  imports Inverse_Schrodinger_Lp_Born_One_Sided_Terminal_Collapse_Base
begin

section \<open>Terminal collapse at every positive branch order\<close>

lemma slp_positive_output_density_terminal_collapse_Suc:
  assumes cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and potential_measurable[measurable]:
      "potential \<in> borel_measurable lborel"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
    and collapse:
      "\<And>inner_origin inner_output.
        slp_positive_output_density R cutoff potential (\<lambda>_. 1) (Suc n)
            inner_origin inner_output \<le>
          ennreal (inverse (pi ^ 2)) * ennreal C *
            (\<integral>\<^sup>+terminal.
              ennreal (slp_localized_cauchy_kernel R
                (terminal - inner_output)) *
              slp_positive_output_density R cutoff potential
                (slp_positive_terminal_riesz_weight R potential) n
                inner_origin terminal
              \<partial>lborel)"
  shows
    "slp_positive_output_density R cutoff potential (\<lambda>_. 1)
        (Suc (Suc n)) origin output \<le>
      ennreal (inverse (pi ^ 2)) * ennreal C *
        (\<integral>\<^sup>+terminal.
          ennreal (slp_localized_cauchy_kernel R (terminal - output)) *
          slp_positive_output_density R cutoff potential
            (slp_positive_terminal_riesz_weight R potential) (Suc n)
            origin terminal
          \<partial>lborel)"
proof -
  note [measurable] = slp_localized_cauchy_kernel_borel_measurable
  let ?coefficient = "ennreal (inverse (pi ^ 2))"
  let ?scale = "?coefficient * ennreal C"
  let ?beta = "slp_positive_terminal_riesz_weight R potential"
  let ?block = "slp_positive_branch_block_weight R cutoff potential origin"
  let ?one_density =
    "slp_positive_output_density R cutoff potential (\<lambda>_. 1) (Suc n)"
  let ?beta_density =
    "slp_positive_output_density R cutoff potential ?beta n"
  let ?test = "\<lambda>terminal.
    ennreal (slp_localized_cauchy_kernel R (terminal - output))"
  let ?convolution = "\<lambda>inner_origin inner_output.
    \<integral>\<^sup>+terminal.
      ennreal (slp_localized_cauchy_kernel R (terminal - inner_output)) *
        ?beta_density inner_origin terminal
      \<partial>lborel"
  have beta_measurable[measurable]: "?beta \<in> borel_measurable lborel"
    by (rule slp_positive_terminal_riesz_weight_measurable[OF
          potential_measurable])
  have block_measurable:
      "case_prod ?block \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by (rule slp_positive_branch_block_weight_measurable;
        measurable)
  have one_density_measurable:
      "case_prod ?one_density \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by (rule slp_positive_output_density_joint_measurable;
        measurable)
  have beta_density_measurable:
      "case_prod ?beta_density \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by (rule slp_positive_output_density_joint_measurable;
        measurable)
  have convolution_measurable:
      "case_prod ?convolution \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    using beta_density_measurable by measurable
  have weighted_convolution_measurable:
      "case_prod (\<lambda>pos_point neg_point.
          ?block pos_point neg_point *
            ?convolution neg_point (output - pos_point + neg_point)) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    using block_measurable convolution_measurable by measurable
  have recursive_integral_le:
      "(\<integral>\<^sup>+pos_point. \<integral>\<^sup>+neg_point.
          ?block pos_point neg_point *
            ?one_density neg_point (output - pos_point + neg_point)
          \<partial>lborel \<partial>lborel) \<le>
        (\<integral>\<^sup>+pos_point. \<integral>\<^sup>+neg_point.
          ?block pos_point neg_point *
            (?scale *
              ?convolution neg_point (output - pos_point + neg_point))
          \<partial>lborel \<partial>lborel)"
    by (intro nn_integral_mono mult_left_mono collapse) simp
  have scaled_pair:
      "(\<integral>\<^sup>+pos_point. \<integral>\<^sup>+neg_point.
          ?block pos_point neg_point *
            (?scale *
              ?convolution neg_point (output - pos_point + neg_point))
          \<partial>lborel \<partial>lborel) =
        ?scale *
          (\<integral>\<^sup>+pos_point. \<integral>\<^sup>+neg_point.
            ?block pos_point neg_point *
              ?convolution neg_point (output - pos_point + neg_point)
            \<partial>lborel \<partial>lborel)"
  proof -
    have inner:
        "(\<integral>\<^sup>+neg_point.
            ?block pos_point neg_point *
              (?scale *
                ?convolution neg_point (output - pos_point + neg_point))
            \<partial>lborel) =
          ?scale *
            (\<integral>\<^sup>+neg_point.
              ?block pos_point neg_point *
                ?convolution neg_point (output - pos_point + neg_point)
              \<partial>lborel)"
      for pos_point
    proof -
      have fiber_measurable:
          "(\<lambda>neg_point.
            ?block pos_point neg_point *
              ?convolution neg_point (output - pos_point + neg_point))
          \<in> borel_measurable lborel"
        using weighted_convolution_measurable by measurable
      show ?thesis
        using nn_integral_cmult[OF fiber_measurable, of ?scale]
        by (simp add: mult.commute mult.left_commute mult.assoc)
    qed
    have outer_measurable:
        "(\<lambda>pos_point. \<integral>\<^sup>+neg_point.
          ?block pos_point neg_point *
            ?convolution neg_point (output - pos_point + neg_point)
          \<partial>lborel) \<in> borel_measurable lborel"
      using weighted_convolution_measurable by measurable
    show ?thesis
      by (simp only: inner nn_integral_cmult[OF outer_measurable])
  qed
  have test_measurable: "?test \<in> borel_measurable lborel"
    by measurable
  have transported:
      "(\<integral>\<^sup>+terminal. ?test terminal *
          (\<integral>\<^sup>+pos_point. \<integral>\<^sup>+neg_point.
            ?block pos_point neg_point *
              ?beta_density neg_point
                (terminal - pos_point + neg_point)
            \<partial>lborel \<partial>lborel)
          \<partial>lborel) =
        (\<integral>\<^sup>+pos_point. \<integral>\<^sup>+neg_point.
          ?block pos_point neg_point *
            (\<integral>\<^sup>+inner_output.
              ?test (inner_output + pos_point - neg_point) *
                ?beta_density neg_point inner_output
              \<partial>lborel)
          \<partial>lborel \<partial>lborel)"
    by (rule slp_nn_integral_affine_output_transport[OF test_measurable
          block_measurable beta_density_measurable])
  have transported_convolution:
      "(\<integral>\<^sup>+pos_point. \<integral>\<^sup>+neg_point.
          ?block pos_point neg_point *
            (\<integral>\<^sup>+inner_output.
              ?test (inner_output + pos_point - neg_point) *
                ?beta_density neg_point inner_output
              \<partial>lborel)
          \<partial>lborel \<partial>lborel) =
        (\<integral>\<^sup>+pos_point. \<integral>\<^sup>+neg_point.
          ?block pos_point neg_point *
            ?convolution neg_point (output - pos_point + neg_point)
          \<partial>lborel \<partial>lborel)"
    by (intro nn_integral_cong)
      (simp add: algebra_simps)
  have target_integrand_measurable:
      "(\<lambda>terminal. ?test terminal *
        (\<integral>\<^sup>+pos_point. \<integral>\<^sup>+neg_point.
          ?block pos_point neg_point *
            ?beta_density neg_point (terminal - pos_point + neg_point)
          \<partial>lborel \<partial>lborel))
      \<in> borel_measurable lborel"
    using test_measurable block_measurable beta_density_measurable
    by measurable
  have target_identity:
      "(\<integral>\<^sup>+terminal. ?test terminal *
          slp_positive_output_density R cutoff potential ?beta (Suc n)
            origin terminal
          \<partial>lborel) =
        ?coefficient *
          (\<integral>\<^sup>+pos_point. \<integral>\<^sup>+neg_point.
            ?block pos_point neg_point *
              ?convolution neg_point (output - pos_point + neg_point)
            \<partial>lborel \<partial>lborel)"
  proof -
    have coefficient_extract:
        "(\<integral>\<^sup>+terminal. ?test terminal *
            (?coefficient *
              (\<integral>\<^sup>+pos_point. \<integral>\<^sup>+neg_point.
                ?block pos_point neg_point *
                  ?beta_density neg_point
                    (terminal - pos_point + neg_point)
                \<partial>lborel \<partial>lborel))
            \<partial>lborel) =
          ?coefficient *
            (\<integral>\<^sup>+terminal. ?test terminal *
              (\<integral>\<^sup>+pos_point. \<integral>\<^sup>+neg_point.
                ?block pos_point neg_point *
                  ?beta_density neg_point
                    (terminal - pos_point + neg_point)
                \<partial>lborel \<partial>lborel)
              \<partial>lborel)"
      using nn_integral_cmult[OF target_integrand_measurable,
          of ?coefficient]
      by (simp add: mult.commute mult.left_commute mult.assoc)
    show ?thesis
      using coefficient_extract transported transported_convolution
      by (simp add: slp_positive_branch_block_weight_def mult.assoc)
  qed
  have density_successor:
      "slp_positive_output_density R cutoff potential (\<lambda>_. 1)
          (Suc (Suc n)) origin output =
        ?coefficient *
          (\<integral>\<^sup>+pos_point. \<integral>\<^sup>+neg_point.
            ?block pos_point neg_point *
              ?one_density neg_point (output - pos_point + neg_point)
            \<partial>lborel \<partial>lborel)"
    by (simp add: slp_positive_branch_block_weight_def mult.assoc)
  have scaled_recursive:
      "?coefficient *
          (\<integral>\<^sup>+pos_point. \<integral>\<^sup>+neg_point.
            ?block pos_point neg_point *
              ?one_density neg_point (output - pos_point + neg_point)
            \<partial>lborel \<partial>lborel) \<le>
        ?coefficient *
          (?scale *
            (\<integral>\<^sup>+pos_point. \<integral>\<^sup>+neg_point.
              ?block pos_point neg_point *
                ?convolution neg_point (output - pos_point + neg_point)
              \<partial>lborel \<partial>lborel))"
    using mult_left_mono[OF recursive_integral_le, of ?coefficient]
      scaled_pair
    by simp
  show ?thesis
    using scaled_recursive density_successor target_identity
    by (simp add: mult.commute mult.left_commute mult.assoc)
qed

theorem slp_positive_output_density_positive_terminal_collapse:
  assumes cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and potential_measurable[measurable]:
      "potential \<in> borel_measurable lborel"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
  shows
    "slp_positive_output_density R cutoff potential (\<lambda>_. 1) (Suc n)
        origin target \<le>
      ennreal (inverse (pi ^ 2)) * ennreal C *
        (\<integral>\<^sup>+terminal.
          ennreal (slp_localized_cauchy_kernel R (terminal - target)) *
          slp_positive_output_density R cutoff potential
            (slp_positive_terminal_riesz_weight R potential) n
            origin terminal
          \<partial>lborel)"
proof (induction n arbitrary: origin target)
  case 0
  show ?case
    using slp_positive_output_density_one_terminal_collapse
      [OF cutoff_measurable potential_measurable cutoff_bound C_nonnegative,
        of R origin target]
    by simp
next
  case (Suc n)
  show ?case
    by (rule slp_positive_output_density_terminal_collapse_Suc;
        fact cutoff_measurable potential_measurable cutoff_bound
          C_nonnegative Suc.IH)
qed

end
