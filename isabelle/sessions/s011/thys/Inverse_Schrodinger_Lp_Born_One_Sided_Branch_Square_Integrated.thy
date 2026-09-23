theory Inverse_Schrodinger_Lp_Born_One_Sided_Branch_Square_Integrated
  imports Inverse_Schrodinger_Lp_Born_One_Sided_Branch_Square
begin

section \<open>Output-integrated square bound for a positive branch successor\<close>

theorem slp_positive_output_square_mass_Suc_le:
  assumes cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and potential_measurable[measurable]:
      "potential \<in> borel_measurable lborel"
    and terminal_weight_measurable[measurable]:
      "terminal_weight \<in> borel_measurable lborel"
  shows
    "slp_positive_output_square_mass R cutoff potential terminal_weight
        (Suc n) origin \<le>
      ennreal (inverse (pi ^ 2)) ^ 2 *
      (\<integral>\<^sup>+pos_point. \<integral>\<^sup>+neg_point.
        slp_positive_branch_block_weight R cutoff potential origin
          pos_point neg_point \<partial>lborel \<partial>lborel) *
      (\<integral>\<^sup>+pos_point. \<integral>\<^sup>+neg_point.
        slp_positive_branch_block_weight R cutoff potential origin
          pos_point neg_point *
        slp_positive_output_square_mass R cutoff potential terminal_weight n
          neg_point
        \<partial>lborel \<partial>lborel)"
proof -
  note [measurable] = slp_localized_cauchy_kernel_borel_measurable
    slp_positive_output_density_joint_measurable[OF cutoff_measurable
      potential_measurable terminal_weight_measurable]
  let ?coefficient = "ennreal (inverse (pi ^ 2)) ^ 2"
  let ?weight =
    "slp_positive_branch_block_weight R cutoff potential origin"
  let ?datum =
    "slp_positive_root_step_datum R cutoff potential terminal_weight n"
  let ?mass = "\<integral>\<^sup>+pos_point. \<integral>\<^sup>+neg_point.
    ?weight pos_point neg_point \<partial>lborel \<partial>lborel"
  let ?square_slice = "\<lambda>output.
    \<integral>\<^sup>+pos_point. \<integral>\<^sup>+neg_point.
      ?weight pos_point neg_point * ?datum output pos_point neg_point ^ 2
      \<partial>lborel \<partial>lborel"
  have square_slice_measurable:
      "?square_slice \<in> borel_measurable lborel"
    unfolding slp_positive_branch_block_weight_def
      slp_positive_root_step_datum_def
    by measurable
  have pointwise:
      "slp_positive_output_density R cutoff potential terminal_weight (Suc n)
          origin out ^ 2 \<le>
        ?coefficient * ?mass * ?square_slice out"
      for out
    by (rule slp_positive_output_density_Suc_squared_le;
        fact cutoff_measurable potential_measurable
          terminal_weight_measurable)
  have integrated:
      "(\<integral>\<^sup>+output.
          slp_positive_output_density R cutoff potential terminal_weight
            (Suc n) origin output ^ 2 \<partial>lborel) \<le>
        (\<integral>\<^sup>+output.
          ?coefficient * ?mass * ?square_slice output \<partial>lborel)"
    by (rule nn_integral_mono; rule pointwise)
  have extract_constant:
      "(\<integral>\<^sup>+output.
          ?coefficient * ?mass * ?square_slice output \<partial>lborel) =
        ?coefficient * ?mass *
          (\<integral>\<^sup>+output. ?square_slice output \<partial>lborel)"
    by (rule nn_integral_cmult[OF square_slice_measurable])
  have transport:
      "(\<integral>\<^sup>+output. ?square_slice output \<partial>lborel) =
        (\<integral>\<^sup>+pos_point. \<integral>\<^sup>+neg_point.
          ?weight pos_point neg_point *
          slp_positive_output_square_mass R cutoff potential terminal_weight n
            neg_point
          \<partial>lborel \<partial>lborel)"
  proof -
    note transported = slp_nn_integral_affine_output_transport[
        where test = "\<lambda>_. 1" and block_weight = ?weight and
          inner_density =
            "\<lambda>neg_point inner_output.
              slp_positive_output_density R cutoff potential terminal_weight n
                neg_point inner_output ^ 2"]
    have block_measurable:
        "case_prod ?weight \<in>
          borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
      unfolding slp_positive_branch_block_weight_def
      by measurable
    have inner_measurable:
        "case_prod (\<lambda>neg_point inner_output.
          slp_positive_output_density R cutoff potential terminal_weight n
            neg_point inner_output ^ 2) \<in>
          borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
      by measurable
    show ?thesis
      using transported[OF _ block_measurable inner_measurable]
      unfolding slp_positive_root_step_datum_def
        slp_positive_output_square_mass_def
      by simp
  qed
  show ?thesis
    using integrated extract_constant transport
    unfolding slp_positive_output_square_mass_def
    by simp
qed

end
