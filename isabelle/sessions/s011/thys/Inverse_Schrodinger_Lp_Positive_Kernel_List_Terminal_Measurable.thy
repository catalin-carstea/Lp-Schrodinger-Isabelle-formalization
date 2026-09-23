theory Inverse_Schrodinger_Lp_Positive_Kernel_List_Terminal_Measurable
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Positive_Kernel_List_Functional_Suc"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_Left_Positive_Kernel_Measurable"
begin

section \<open>Terminal measurability of a fixed positive list kernel\<close>

theorem slp_left_branch_positive_kernel_list_terminal_measurable:
  assumes cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and potential_measurable[measurable]:
      "potential \<in> borel_measurable lborel"
    and terminal_value_measurable[measurable]:
      "terminal_value \<in> borel_measurable lborel"
  shows
    "slp_left_branch_positive_kernel_list R cutoff potential terminal_value
        pairs origin \<in> borel_measurable lborel"
proof -
  let ?pair_functions = "map (\<lambda>pair (_::slp_point). pair) pairs"
  have pair_first:
      "\<And>pair_function. pair_function \<in> set ?pair_functions \<Longrightarrow>
        (\<lambda>terminal. fst (pair_function terminal))
          \<in> measurable lborel lborel"
  proof -
    fix pair_function
    assume "pair_function \<in> set ?pair_functions"
    then obtain pair where
        "pair_function = (\<lambda>_::slp_point. pair)"
      by auto
    then show "(\<lambda>terminal. fst (pair_function terminal))
        \<in> measurable lborel lborel"
      by simp
  qed
  have pair_second:
      "\<And>pair_function. pair_function \<in> set ?pair_functions \<Longrightarrow>
        (\<lambda>terminal. snd (pair_function terminal))
          \<in> measurable lborel lborel"
  proof -
    fix pair_function
    assume "pair_function \<in> set ?pair_functions"
    then obtain pair where
        "pair_function = (\<lambda>_::slp_point. pair)"
      by auto
    then show "(\<lambda>terminal. snd (pair_function terminal))
        \<in> measurable lborel lborel"
      by simp
  qed
  have origin_measurable:
      "(\<lambda>_::slp_point. origin) \<in> measurable lborel lborel"
    by measurable
  have terminal_measurable:
      "id \<in> measurable lborel lborel"
    by measurable
  have parameterized:
      "(\<lambda>terminal. slp_left_branch_positive_kernel_list R cutoff
          potential terminal_value
          (map (\<lambda>pair_function. pair_function terminal) ?pair_functions)
          ((\<lambda>_. origin) terminal) (id terminal))
        \<in> borel_measurable lborel"
    by (rule slp_left_branch_positive_kernel_list_param_measurable[OF
          cutoff_measurable potential_measurable terminal_value_measurable
          origin_measurable terminal_measurable pair_first pair_second])
  show ?thesis
    using parameterized
    by (simp only: map_map comp_def id_apply map_ident)
qed

end
