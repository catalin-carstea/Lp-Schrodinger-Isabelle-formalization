theory Inverse_Schrodinger_Lp_Born_One_Sided_Step_Square
  imports Inverse_Schrodinger_Lp_Weighted_NN_Integral_Pair
begin

section \<open>Pointwise square bound for the positive root step\<close>

definition slp_positive_root_step_weight ::
    "real \<Rightarrow> (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      slp_point \<Rightarrow> slp_point \<Rightarrow> ennreal"
where
  "slp_positive_root_step_weight R cutoff potential root_weight pos_point
      neg_point =
    ennreal (slp_localized_riesz_potential R root_weight pos_point) *
    ennreal (norm (cutoff pos_point)) *
    ennreal (slp_localized_cauchy_kernel R (pos_point - neg_point)) *
    ennreal (norm (potential neg_point))"

definition slp_positive_root_step_datum ::
    "real \<Rightarrow> (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> ennreal) \<Rightarrow> nat \<Rightarrow>
      slp_point \<Rightarrow> slp_point \<Rightarrow> slp_point \<Rightarrow> ennreal"
where
  "slp_positive_root_step_datum R cutoff potential terminal_weight n output
      pos_point neg_point =
    slp_positive_output_density R cutoff potential terminal_weight n neg_point
      (output - pos_point + neg_point)"

theorem slp_positive_root_step_density_squared_le:
  assumes cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and potential_measurable[measurable]:
      "potential \<in> borel_measurable lborel"
    and terminal_weight_measurable[measurable]:
      "terminal_weight \<in> borel_measurable lborel"
    and root_weight_measurable[measurable]:
      "root_weight \<in> borel_measurable lborel"
  shows
    "slp_positive_root_step_density R cutoff potential terminal_weight n
        root_weight output ^ 2 \<le>
      ennreal (inverse (pi ^ 2)) ^ 2 *
      (\<integral>\<^sup>+pos_point. \<integral>\<^sup>+neg_point.
        slp_positive_root_step_weight R cutoff potential root_weight
          pos_point neg_point \<partial>lborel \<partial>lborel) *
      (\<integral>\<^sup>+pos_point. \<integral>\<^sup>+neg_point.
        slp_positive_root_step_weight R cutoff potential root_weight
          pos_point neg_point *
        slp_positive_root_step_datum R cutoff potential terminal_weight n
          output pos_point neg_point ^ 2
        \<partial>lborel \<partial>lborel)"
proof -
  note [measurable] = slp_localized_riesz_potential_measurable[
      OF root_weight_measurable]
    slp_localized_cauchy_kernel_borel_measurable
    slp_positive_output_density_joint_measurable[OF cutoff_measurable
      potential_measurable terminal_weight_measurable]
  have weighted_square:
      "(\<integral>\<^sup>+pos_point. \<integral>\<^sup>+neg_point.
          slp_positive_root_step_weight R cutoff potential root_weight
            pos_point neg_point *
          slp_positive_root_step_datum R cutoff potential terminal_weight n
            output pos_point neg_point
          \<partial>lborel \<partial>lborel) ^ 2 \<le>
        (\<integral>\<^sup>+pos_point. \<integral>\<^sup>+neg_point.
          slp_positive_root_step_weight R cutoff potential root_weight
            pos_point neg_point \<partial>lborel \<partial>lborel) *
        (\<integral>\<^sup>+pos_point. \<integral>\<^sup>+neg_point.
          slp_positive_root_step_weight R cutoff potential root_weight
            pos_point neg_point *
          slp_positive_root_step_datum R cutoff potential terminal_weight n
            output pos_point neg_point ^ 2
          \<partial>lborel \<partial>lborel)"
    unfolding slp_positive_root_step_weight_def
      slp_positive_root_step_datum_def
    by (rule slp_nn_integral_weighted_cauchy_schwarz_pair; measurable)
  have step_identity:
      "slp_positive_root_step_density R cutoff potential terminal_weight n
          root_weight output =
        ennreal (inverse (pi ^ 2)) *
        (\<integral>\<^sup>+pos_point. \<integral>\<^sup>+neg_point.
          slp_positive_root_step_weight R cutoff potential root_weight
            pos_point neg_point *
          slp_positive_root_step_datum R cutoff potential terminal_weight n
            output pos_point neg_point
          \<partial>lborel \<partial>lborel)"
    unfolding slp_positive_root_step_density_def
      slp_positive_root_step_weight_def
      slp_positive_root_step_datum_def
    by (simp add: mult.assoc)
  show ?thesis
  proof (subst step_identity)
    have coefficient_nonnegative:
        "0 \<le> ennreal (inverse (pi ^ 2)) ^ 2"
      by simp
    show
      "(ennreal (inverse (pi ^ 2)) *
          (\<integral>\<^sup>+pos_point. \<integral>\<^sup>+neg_point.
            slp_positive_root_step_weight R cutoff potential root_weight
              pos_point neg_point *
            slp_positive_root_step_datum R cutoff potential terminal_weight n
              output pos_point neg_point
            \<partial>lborel \<partial>lborel)) ^ 2 \<le>
        ennreal (inverse (pi ^ 2)) ^ 2 *
        (\<integral>\<^sup>+pos_point. \<integral>\<^sup>+neg_point.
          slp_positive_root_step_weight R cutoff potential root_weight
            pos_point neg_point \<partial>lborel \<partial>lborel) *
        (\<integral>\<^sup>+pos_point. \<integral>\<^sup>+neg_point.
          slp_positive_root_step_weight R cutoff potential root_weight
            pos_point neg_point *
          slp_positive_root_step_datum R cutoff potential terminal_weight n
            output pos_point neg_point ^ 2
          \<partial>lborel \<partial>lborel)"
      using mult_left_mono[OF weighted_square coefficient_nonnegative]
      by (simp add: power_mult_distrib mult.assoc)
  qed
qed

end
