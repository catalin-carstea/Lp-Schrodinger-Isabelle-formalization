theory Inverse_Schrodinger_Lp_Left_Oscillatory_Graph_Integrable
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_002.Inverse_Schrodinger_Lp_Left_Nested_Graph_Functional"
begin

section \<open>Fixed-list oscillation preserves terminal integrability\<close>

lemma slp_left_branch_oscillatory_graph_kernel_norm:
  "norm (slp_left_branch_oscillatory_graph_kernel tau center cutoff
      potential terminal_value pairs origin terminal) =
    norm (slp_left_branch_complex_kernel_list cutoff potential terminal_value
      pairs origin terminal)"
  unfolding slp_left_branch_oscillatory_graph_kernel_def
  by (simp only: norm_mult norm_exp_i_times mult_1_left)

lemma slp_left_branch_oscillatory_graph_kernel_terminal_measurable:
  assumes cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and potential_measurable[measurable]:
      "potential \<in> borel_measurable lborel"
    and terminal_value_measurable[measurable]:
      "terminal_value \<in> borel_measurable lborel"
  shows
    "slp_left_branch_oscillatory_graph_kernel tau center cutoff potential
        terminal_value pairs origin \<in> borel_measurable lborel"
proof -
  have phase_measurable[measurable]:
      "(\<lambda>terminal. slp_left_branch_phase center pairs terminal)
        \<in> borel_measurable lborel"
    unfolding slp_left_branch_phase_def slp_branch_phase_def
    using slp_center_phase_measurable[of center]
    by measurable
  have raw_measurable[measurable]:
      "slp_left_branch_complex_kernel_list cutoff potential terminal_value
          pairs origin \<in> borel_measurable lborel"
    by (rule slp_left_branch_complex_kernel_list_measurable[OF
          cutoff_measurable potential_measurable terminal_value_measurable])
  show ?thesis
    unfolding slp_left_branch_oscillatory_graph_kernel_def
    by measurable
qed

theorem slp_left_branch_oscillatory_graph_kernel_integrable_iff:
  assumes cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and potential_measurable[measurable]:
      "potential \<in> borel_measurable lborel"
    and terminal_value_measurable[measurable]:
      "terminal_value \<in> borel_measurable lborel"
  shows
    "integrable lborel
        (slp_left_branch_oscillatory_graph_kernel tau center cutoff potential
          terminal_value pairs origin) \<longleftrightarrow>
      integrable lborel
        (slp_left_branch_complex_kernel_list cutoff potential terminal_value
          pairs origin)"
proof -
  have oscillatory_measurable:
      "slp_left_branch_oscillatory_graph_kernel tau center cutoff potential
          terminal_value pairs origin \<in> borel_measurable lborel"
    by (rule slp_left_branch_oscillatory_graph_kernel_terminal_measurable[OF
          cutoff_measurable potential_measurable terminal_value_measurable])
  have raw_measurable:
      "slp_left_branch_complex_kernel_list cutoff potential terminal_value
          pairs origin \<in> borel_measurable lborel"
    by (rule slp_left_branch_complex_kernel_list_measurable[OF
          cutoff_measurable potential_measurable terminal_value_measurable])
  have norm_mass:
      "(\<integral>\<^sup>+ terminal.
          ennreal (norm (slp_left_branch_oscillatory_graph_kernel tau center
            cutoff potential terminal_value pairs origin terminal))
        \<partial>lborel) =
       (\<integral>\<^sup>+ terminal.
          ennreal (norm (slp_left_branch_complex_kernel_list cutoff potential
            terminal_value pairs origin terminal))
        \<partial>lborel)"
    by (rule nn_integral_cong)
      (simp only: slp_left_branch_oscillatory_graph_kernel_norm)
  show ?thesis
    unfolding integrable_iff_bounded
    by (simp only: oscillatory_measurable raw_measurable norm_mass)
qed

end
