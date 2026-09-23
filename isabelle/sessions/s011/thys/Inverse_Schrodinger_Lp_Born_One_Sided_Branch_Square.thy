theory Inverse_Schrodinger_Lp_Born_One_Sided_Branch_Square
  imports Inverse_Schrodinger_Lp_Born_One_Sided_Step_Mass_Finite
begin

section \<open>Pointwise square bound for a positive branch successor\<close>

theorem slp_positive_output_density_Suc_squared_le:
  assumes cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and potential_measurable[measurable]:
      "potential \<in> borel_measurable lborel"
    and terminal_weight_measurable[measurable]:
      "terminal_weight \<in> borel_measurable lborel"
  shows
    "slp_positive_output_density R cutoff potential terminal_weight (Suc n)
        origin output ^ 2 \<le>
      ennreal (inverse (pi ^ 2)) ^ 2 *
      (\<integral>\<^sup>+pos_point. \<integral>\<^sup>+neg_point.
        slp_positive_branch_block_weight R cutoff potential origin
          pos_point neg_point \<partial>lborel \<partial>lborel) *
      (\<integral>\<^sup>+pos_point. \<integral>\<^sup>+neg_point.
        slp_positive_branch_block_weight R cutoff potential origin
          pos_point neg_point *
        slp_positive_root_step_datum R cutoff potential terminal_weight n
          output pos_point neg_point ^ 2
        \<partial>lborel \<partial>lborel)"
proof -
  note [measurable] = slp_localized_cauchy_kernel_borel_measurable
    slp_positive_output_density_joint_measurable[OF cutoff_measurable
      potential_measurable terminal_weight_measurable]
  have weighted_square:
      "(\<integral>\<^sup>+pos_point. \<integral>\<^sup>+neg_point.
          slp_positive_branch_block_weight R cutoff potential origin
            pos_point neg_point *
          slp_positive_root_step_datum R cutoff potential terminal_weight n
            output pos_point neg_point
          \<partial>lborel \<partial>lborel) ^ 2 \<le>
        (\<integral>\<^sup>+pos_point. \<integral>\<^sup>+neg_point.
          slp_positive_branch_block_weight R cutoff potential origin
            pos_point neg_point \<partial>lborel \<partial>lborel) *
        (\<integral>\<^sup>+pos_point. \<integral>\<^sup>+neg_point.
          slp_positive_branch_block_weight R cutoff potential origin
            pos_point neg_point *
          slp_positive_root_step_datum R cutoff potential terminal_weight n
            output pos_point neg_point ^ 2
          \<partial>lborel \<partial>lborel)"
    unfolding slp_positive_branch_block_weight_def
      slp_positive_root_step_datum_def
    by (rule slp_nn_integral_weighted_cauchy_schwarz_pair; measurable)
  have successor_identity:
      "slp_positive_output_density R cutoff potential terminal_weight (Suc n)
          origin output =
        ennreal (inverse (pi ^ 2)) *
        (\<integral>\<^sup>+pos_point. \<integral>\<^sup>+neg_point.
          slp_positive_branch_block_weight R cutoff potential origin
            pos_point neg_point *
          slp_positive_root_step_datum R cutoff potential terminal_weight n
            output pos_point neg_point
          \<partial>lborel \<partial>lborel)"
    unfolding slp_positive_branch_block_weight_def
      slp_positive_root_step_datum_def by (simp add: mult.assoc)
  have coefficient_nonnegative:
      "0 \<le> ennreal (inverse (pi ^ 2)) ^ 2"
    by simp
  have scaled_square:
      "(ennreal (inverse (pi ^ 2)) *
          (\<integral>\<^sup>+pos_point. \<integral>\<^sup>+neg_point.
            slp_positive_branch_block_weight R cutoff potential origin
              pos_point neg_point *
            slp_positive_root_step_datum R cutoff potential terminal_weight n
              output pos_point neg_point
            \<partial>lborel \<partial>lborel)) ^ 2 \<le>
        ennreal (inverse (pi ^ 2)) ^ 2 *
        (\<integral>\<^sup>+pos_point. \<integral>\<^sup>+neg_point.
          slp_positive_branch_block_weight R cutoff potential origin
            pos_point neg_point \<partial>lborel \<partial>lborel) *
        (\<integral>\<^sup>+pos_point. \<integral>\<^sup>+neg_point.
          slp_positive_branch_block_weight R cutoff potential origin
            pos_point neg_point *
          slp_positive_root_step_datum R cutoff potential terminal_weight n
            output pos_point neg_point ^ 2
          \<partial>lborel \<partial>lborel)"
    using mult_left_mono[OF weighted_square coefficient_nonnegative]
    by (simp only: power_mult_distrib mult.assoc)
  show ?thesis
    using scaled_square by (simp only: successor_identity)
qed

end
