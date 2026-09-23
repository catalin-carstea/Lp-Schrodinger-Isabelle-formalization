theory Inverse_Schrodinger_Lp_Born_One_Sided_Step_Square_Integrated
  imports Inverse_Schrodinger_Lp_Born_One_Sided_Step_Square
    Inverse_Schrodinger_Lp_Affine_Output_Transport
begin

section \<open>Output-integrated square bound for the positive root step\<close>

definition slp_positive_output_square_mass ::
    "real \<Rightarrow> (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> ennreal) \<Rightarrow> nat \<Rightarrow>
      slp_point \<Rightarrow> ennreal"
where
  "slp_positive_output_square_mass R cutoff potential terminal_weight n
      origin =
    (\<integral>\<^sup>+output.
      slp_positive_output_density R cutoff potential terminal_weight n origin
        output ^ 2 \<partial>lborel)"

theorem slp_positive_root_step_density_square_integral_le:
  assumes cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and potential_measurable[measurable]:
      "potential \<in> borel_measurable lborel"
    and terminal_weight_measurable[measurable]:
      "terminal_weight \<in> borel_measurable lborel"
    and root_weight_measurable[measurable]:
      "root_weight \<in> borel_measurable lborel"
  shows
    "(\<integral>\<^sup>+output.
        slp_positive_root_step_density R cutoff potential terminal_weight n
          root_weight output ^ 2 \<partial>lborel) \<le>
      ennreal (inverse (pi ^ 2)) ^ 2 *
      (\<integral>\<^sup>+pos_point. \<integral>\<^sup>+neg_point.
        slp_positive_root_step_weight R cutoff potential root_weight
          pos_point neg_point \<partial>lborel \<partial>lborel) *
      (\<integral>\<^sup>+pos_point. \<integral>\<^sup>+neg_point.
        slp_positive_root_step_weight R cutoff potential root_weight
          pos_point neg_point *
        slp_positive_output_square_mass R cutoff potential terminal_weight n
          neg_point
        \<partial>lborel \<partial>lborel)"
proof -
  note [measurable] = slp_localized_riesz_potential_measurable[
      OF root_weight_measurable]
    slp_localized_cauchy_kernel_borel_measurable
    slp_positive_output_density_joint_measurable[OF cutoff_measurable
      potential_measurable terminal_weight_measurable]
  let ?coefficient = "ennreal (inverse (pi ^ 2)) ^ 2"
  let ?weight =
    "slp_positive_root_step_weight R cutoff potential root_weight"
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
    unfolding slp_positive_root_step_weight_def
      slp_positive_root_step_datum_def
    by measurable
  have pointwise:
      "slp_positive_root_step_density R cutoff potential terminal_weight n
          root_weight out ^ 2 \<le>
        ?coefficient * ?mass * ?square_slice out"
      for out
    by (rule slp_positive_root_step_density_squared_le;
        fact cutoff_measurable potential_measurable
          terminal_weight_measurable root_weight_measurable)
  have integrated:
      "(\<integral>\<^sup>+output.
          slp_positive_root_step_density R cutoff potential terminal_weight n
            root_weight output ^ 2 \<partial>lborel) \<le>
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
      unfolding slp_positive_root_step_weight_def
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
    using integrated extract_constant transport by simp
qed

end
