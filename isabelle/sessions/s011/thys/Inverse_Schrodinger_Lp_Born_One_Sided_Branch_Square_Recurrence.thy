theory Inverse_Schrodinger_Lp_Born_One_Sided_Branch_Square_Recurrence
  imports Inverse_Schrodinger_Lp_Born_One_Sided_Branch_Square_Integrated
begin

section \<open>Quantitative uniform branch square recurrence\<close>

theorem slp_positive_output_square_mass_Suc_recurrence:
  assumes cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and potential_measurable[measurable]:
      "potential \<in> borel_measurable lborel"
    and terminal_weight_measurable[measurable]:
      "terminal_weight \<in> borel_measurable lborel"
    and block_mass_bound:
      "\<And>origin.
        (\<integral>\<^sup>+pos_point. \<integral>\<^sup>+neg_point.
          slp_positive_branch_block_weight R cutoff potential origin
            pos_point neg_point \<partial>lborel \<partial>lborel) \<le> B"
    and recursive_square_bound:
      "\<And>origin.
        slp_positive_output_square_mass R cutoff potential terminal_weight n
          origin \<le> L"
  shows
    "slp_positive_output_square_mass R cutoff potential terminal_weight
        (Suc n) origin \<le>
      ennreal (inverse (pi ^ 2)) ^ 2 * B ^ 2 * L"
proof -
  note [measurable] = slp_localized_cauchy_kernel_borel_measurable
    slp_positive_output_density_joint_measurable[OF cutoff_measurable
      potential_measurable terminal_weight_measurable]
  let ?weight =
    "slp_positive_branch_block_weight R cutoff potential origin"
  let ?square_mass =
    "slp_positive_output_square_mass R cutoff potential terminal_weight n"
  let ?mass =
    "\<integral>\<^sup>+pos_point. \<integral>\<^sup>+neg_point.
      ?weight pos_point neg_point \<partial>lborel \<partial>lborel"
  let ?weighted_square =
    "\<integral>\<^sup>+pos_point. \<integral>\<^sup>+neg_point.
      ?weight pos_point neg_point * ?square_mass neg_point
      \<partial>lborel \<partial>lborel"
  have weight_joint_measurable:
      "case_prod ?weight \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    unfolding slp_positive_branch_block_weight_def
    by measurable
  have weighted_square_le_scaled_mass:
      "?weighted_square \<le> ?mass * L"
  proof -
    have monotone:
        "?weighted_square \<le>
          (\<integral>\<^sup>+pos_point. \<integral>\<^sup>+neg_point.
            ?weight pos_point neg_point * L \<partial>lborel \<partial>lborel)"
      by (intro nn_integral_mono mult_left_mono recursive_square_bound) simp
    have extraction:
        "(\<integral>\<^sup>+pos_point. \<integral>\<^sup>+neg_point.
            ?weight pos_point neg_point * L \<partial>lborel \<partial>lborel) =
          ?mass * L"
    proof -
      have inner:
          "(\<integral>\<^sup>+neg_point. ?weight pos_point neg_point * L
              \<partial>lborel) =
            (\<integral>\<^sup>+neg_point. ?weight pos_point neg_point
              \<partial>lborel) * L"
          for pos_point
      proof (rule nn_integral_multc)
        show "(\<lambda>neg_point. ?weight pos_point neg_point)
            \<in> borel_measurable lborel"
          unfolding slp_positive_branch_block_weight_def
          by measurable
      qed
      have outer_measurable:
          "(\<lambda>pos_point. \<integral>\<^sup>+neg_point.
            ?weight pos_point neg_point \<partial>lborel)
          \<in> borel_measurable lborel"
        unfolding slp_positive_branch_block_weight_def
        by measurable
      show ?thesis
        by (simp only: inner nn_integral_multc[OF outer_measurable])
    qed
    show ?thesis using monotone extraction by simp
  qed
  have weighted_square_bound: "?weighted_square \<le> B * L"
    by (rule order_trans[OF weighted_square_le_scaled_mass])
      (rule mult_right_mono[OF block_mass_bound], simp)
  have integrated:
      "slp_positive_output_square_mass R cutoff potential terminal_weight
          (Suc n) origin \<le>
        ennreal (inverse (pi ^ 2)) ^ 2 * ?mass * ?weighted_square"
    by (rule slp_positive_output_square_mass_Suc_le;
        fact cutoff_measurable potential_measurable
          terminal_weight_measurable)
  have scale_weighted:
      "ennreal (inverse (pi ^ 2)) ^ 2 * ?mass * ?weighted_square \<le>
        ennreal (inverse (pi ^ 2)) ^ 2 * ?mass * (B * L)"
    by (rule mult_left_mono[OF weighted_square_bound]) simp
  have scale_mass:
      "ennreal (inverse (pi ^ 2)) ^ 2 * ?mass * (B * L) \<le>
        ennreal (inverse (pi ^ 2)) ^ 2 * B * (B * L)"
    using mult_right_mono[OF mult_left_mono[OF block_mass_bound, of
          "ennreal (inverse (pi ^ 2)) ^ 2"]]
    by (simp add: mult.assoc)
  show ?thesis
    using order_trans[OF integrated order_trans[OF scale_weighted scale_mass]]
    by (simp add: power2_eq_square mult.assoc)
qed

end
