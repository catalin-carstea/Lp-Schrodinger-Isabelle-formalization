theory Inverse_Schrodinger_Lp_Born_Branch_Mass_Bound
  imports Inverse_Schrodinger_Lp_Born_Branch_Mass
begin

section \<open>One-step positive branch mass bound\<close>

theorem slp_positive_branch_mass_Suc_le:
  assumes cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_measurable: "potential \<in> borel_measurable lborel"
    and previous_bound:
      "\<And>neg_point.
        slp_positive_branch_functional R cutoff potential terminal_weight n
          neg_point (\<lambda>_. 1) \<le> M"
  shows
    "slp_positive_branch_functional R cutoff potential terminal_weight (Suc n)
        origin (\<lambda>_. 1) \<le>
      ennreal (inverse (pi ^ 2)) *
        ((\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
            slp_positive_branch_block_weight R cutoff potential origin
              pos_point neg_point
            \<partial>lborel \<partial>lborel) * M)"
proof -
  have block_joint[measurable]:
      "case_prod
          (slp_positive_branch_block_weight R cutoff potential origin)
        \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by (rule slp_positive_branch_block_weight_measurable[OF
          cutoff_measurable potential_measurable])
  have block_slice[measurable]:
      "(\<lambda>neg_point.
          slp_positive_branch_block_weight R cutoff potential origin
            pos_point neg_point) \<in> borel_measurable lborel"
    for pos_point
    by measurable
  have block_integral_measurable[measurable]:
      "(\<lambda>pos_point. \<integral>\<^sup>+ neg_point.
          slp_positive_branch_block_weight R cutoff potential origin
            pos_point neg_point
          \<partial>lborel) \<in> borel_measurable lborel"
    by measurable
  have recursive_integral_le:
      "(\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
          slp_positive_branch_block_weight R cutoff potential origin pos_point
            neg_point *
          slp_positive_branch_functional R cutoff potential terminal_weight n
            neg_point (\<lambda>_. 1)
          \<partial>lborel \<partial>lborel) \<le>
        (\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
          slp_positive_branch_block_weight R cutoff potential origin pos_point
            neg_point * M
          \<partial>lborel \<partial>lborel)"
  proof (rule nn_integral_mono)
    fix pos_point :: slp_point
    assume "pos_point \<in> space lborel"
    show "(\<integral>\<^sup>+ neg_point.
        slp_positive_branch_block_weight R cutoff potential origin pos_point
          neg_point *
        slp_positive_branch_functional R cutoff potential terminal_weight n
          neg_point (\<lambda>_. 1)
        \<partial>lborel) \<le>
      (\<integral>\<^sup>+ neg_point.
        slp_positive_branch_block_weight R cutoff potential origin pos_point
          neg_point * M
        \<partial>lborel)"
    proof (rule nn_integral_mono)
      fix neg_point :: slp_point
      assume "neg_point \<in> space lborel"
      show "slp_positive_branch_block_weight R cutoff potential origin
          pos_point neg_point *
          slp_positive_branch_functional R cutoff potential terminal_weight n
            neg_point (\<lambda>_. 1) \<le>
        slp_positive_branch_block_weight R cutoff potential origin pos_point
          neg_point * M"
        by (rule mult_left_mono[OF previous_bound[of neg_point]]) simp
    qed
  qed
  have scaled_integral:
      "(\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
          slp_positive_branch_block_weight R cutoff potential origin pos_point
            neg_point * M
          \<partial>lborel \<partial>lborel) =
        (\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
          slp_positive_branch_block_weight R cutoff potential origin pos_point
            neg_point
          \<partial>lborel \<partial>lborel) * M"
  proof -
    have inner:
        "(\<integral>\<^sup>+ neg_point.
            slp_positive_branch_block_weight R cutoff potential origin
              pos_point neg_point * M
            \<partial>lborel) =
          (\<integral>\<^sup>+ neg_point.
            slp_positive_branch_block_weight R cutoff potential origin
              pos_point neg_point
            \<partial>lborel) * M"
      for pos_point
      by (rule nn_integral_multc[OF block_slice])
    show ?thesis
      by (simp only: inner nn_integral_multc[OF block_integral_measurable])
  qed
  show ?thesis
    unfolding slp_positive_branch_mass_Suc
  proof (rule mult_left_mono)
    show "(\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
        slp_positive_branch_block_weight R cutoff potential origin pos_point
          neg_point *
        slp_positive_branch_functional R cutoff potential terminal_weight n
          neg_point (\<lambda>_. 1)
        \<partial>lborel \<partial>lborel) \<le>
      (\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
        slp_positive_branch_block_weight R cutoff potential origin pos_point
          neg_point
        \<partial>lborel \<partial>lborel) * M"
      using recursive_integral_le scaled_integral by simp
    show "0 \<le> ennreal (inverse (pi ^ 2))"
      by (rule zero_le)
  qed
qed

corollary slp_positive_branch_mass_Suc_less_top:
  assumes cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_measurable: "potential \<in> borel_measurable lborel"
    and previous_bound:
      "\<And>neg_point.
        slp_positive_branch_functional R cutoff potential terminal_weight n
          neg_point (\<lambda>_. 1) \<le> M"
    and M_finite: "M < top"
    and block_finite:
      "(\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
          slp_positive_branch_block_weight R cutoff potential origin pos_point
            neg_point
          \<partial>lborel \<partial>lborel) < top"
  shows
    "slp_positive_branch_functional R cutoff potential terminal_weight (Suc n)
        origin (\<lambda>_. 1) < top"
proof (rule order_le_less_trans)
  show "slp_positive_branch_functional R cutoff potential terminal_weight
      (Suc n) origin (\<lambda>_. 1) \<le>
    ennreal (inverse (pi ^ 2)) *
      ((\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
          slp_positive_branch_block_weight R cutoff potential origin pos_point
            neg_point
          \<partial>lborel \<partial>lborel) * M)"
    by (rule slp_positive_branch_mass_Suc_le[OF cutoff_measurable
          potential_measurable previous_bound])
  show "ennreal (inverse (pi ^ 2)) *
      ((\<integral>\<^sup>+ pos_point. \<integral>\<^sup>+ neg_point.
          slp_positive_branch_block_weight R cutoff potential origin pos_point
            neg_point
          \<partial>lborel \<partial>lborel) * M) < top"
    using M_finite block_finite by (simp add: ennreal_mult_less_top)
qed

end
