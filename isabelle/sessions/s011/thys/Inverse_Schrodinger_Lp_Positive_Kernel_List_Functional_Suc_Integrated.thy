theory Inverse_Schrodinger_Lp_Positive_Kernel_List_Functional_Suc_Integrated
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Positive_Kernel_List_Terminal_Measurable"
begin

section \<open>Integrated successor decomposition of the positive list kernel\<close>

theorem slp_left_branch_positive_kernel_list_Suc_integral:
  assumes cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and potential_measurable[measurable]:
      "potential \<in> borel_measurable lborel"
    and terminal_value_measurable[measurable]:
      "terminal_value \<in> borel_measurable lborel"
    and output_factor_measurable[measurable]:
      "output_factor \<in> borel_measurable lborel"
  shows
    "(\<integral>\<^sup>+ terminal.
        slp_left_branch_positive_kernel_list R cutoff potential terminal_value
            (pair # pairs) origin terminal *
          ennreal (norm (output_factor
            (slp_left_branch_output (pair # pairs) terminal)))
        \<partial>lborel) =
      ennreal (inverse (pi ^ 2)) *
        slp_positive_branch_block_weight R cutoff potential origin
          (fst pair) (snd pair) *
        (\<integral>\<^sup>+ terminal.
          slp_left_branch_positive_kernel_list R cutoff potential terminal_value
              pairs (snd pair) terminal *
            ennreal (norm (output_factor
              (slp_left_branch_output pairs terminal + fst pair - snd pair)))
          \<partial>lborel)"
proof -
  have output_point_measurable:
      "(\<lambda>terminal. slp_left_branch_output pairs terminal +
          fst pair - snd pair) \<in> measurable lborel lborel"
    unfolding slp_left_branch_output_def
    by measurable
  have output_value_measurable[measurable]:
      "(\<lambda>terminal. output_factor
          (slp_left_branch_output pairs terminal + fst pair - snd pair))
        \<in> borel_measurable lborel"
    using measurable_comp[OF output_point_measurable output_factor_measurable]
    by (simp only: comp_def)
  have tail_kernel_measurable[measurable]:
      "slp_left_branch_positive_kernel_list R cutoff potential terminal_value
          pairs (snd pair) \<in> borel_measurable lborel"
    by (rule slp_left_branch_positive_kernel_list_terminal_measurable[OF
          cutoff_measurable potential_measurable terminal_value_measurable])
  have tail_integrand_measurable:
      "(\<lambda>terminal.
        slp_left_branch_positive_kernel_list R cutoff potential terminal_value
            pairs (snd pair) terminal *
          ennreal (norm (output_factor
            (slp_left_branch_output pairs terminal + fst pair - snd pair))))
        \<in> borel_measurable lborel"
    by measurable
  have pointwise:
      "\<And>terminal.
        slp_left_branch_positive_kernel_list R cutoff potential terminal_value
            (pair # pairs) origin terminal *
          ennreal (norm (output_factor
            (slp_left_branch_output (pair # pairs) terminal))) =
        ennreal (inverse (pi ^ 2)) *
          slp_positive_branch_block_weight R cutoff potential origin
            (fst pair) (snd pair) *
          (slp_left_branch_positive_kernel_list R cutoff potential
              terminal_value pairs (snd pair) terminal *
            ennreal (norm (output_factor
              (slp_left_branch_output pairs terminal + fst pair - snd pair))))"
    by (rule slp_left_branch_positive_kernel_list_Suc_integrand)
  show ?thesis
    apply (subst nn_integral_cong[OF pointwise])
    by (simp only: nn_integral_cmult[OF tail_integrand_measurable])
qed

end
