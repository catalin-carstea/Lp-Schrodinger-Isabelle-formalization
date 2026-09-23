theory Inverse_Schrodinger_Lp_Born_Branch_Outputs
  imports Inverse_Schrodinger_Lp_Raw_Power_Error_Closure
begin

section \<open>Finite Born-branch output records\<close>

definition slp_branch_increment ::
    "(slp_point \<times> slp_point) \<Rightarrow> slp_point" where
  "slp_branch_increment pair = fst pair - snd pair"

definition slp_left_branch_output ::
    "(slp_point \<times> slp_point) list \<Rightarrow> slp_point \<Rightarrow> slp_point" where
  "slp_left_branch_output pairs terminal =
    terminal + sum_list (map slp_branch_increment pairs)"

definition slp_right_branch_output ::
    "(slp_point \<times> slp_point) list \<Rightarrow> slp_point \<Rightarrow> slp_point" where
  "slp_right_branch_output pairs terminal =
    terminal + sum_list (map slp_branch_increment pairs)"

definition slp_mixed_branch_center ::
    "slp_point \<Rightarrow>
      (slp_point \<times> slp_point) list \<Rightarrow> slp_point \<Rightarrow>
      (slp_point \<times> slp_point) list \<Rightarrow> slp_point \<Rightarrow> slp_point" where
  "slp_mixed_branch_center origin left_pairs left_terminal
      right_pairs right_terminal =
    - origin + slp_left_branch_output left_pairs left_terminal +
      slp_right_branch_output right_pairs right_terminal"

lemma slp_left_branch_output_Nil [simp]:
  "slp_left_branch_output [] terminal = terminal"
  by (simp add: slp_left_branch_output_def)

lemma slp_right_branch_output_Nil [simp]:
  "slp_right_branch_output [] terminal = terminal"
  by (simp add: slp_right_branch_output_def)

lemma slp_left_branch_output_Cons [simp]:
  "slp_left_branch_output (pair # pairs) terminal =
    slp_branch_increment pair + slp_left_branch_output pairs terminal"
  by (simp add: slp_left_branch_output_def algebra_simps)

lemma slp_right_branch_output_Cons [simp]:
  "slp_right_branch_output (pair # pairs) terminal =
    slp_branch_increment pair + slp_right_branch_output pairs terminal"
  by (simp add: slp_right_branch_output_def algebra_simps)

lemma slp_left_branch_output_append:
  "slp_left_branch_output (left @ right) terminal =
    slp_left_branch_output left 0 + slp_left_branch_output right terminal"
  by (simp add: slp_left_branch_output_def algebra_simps)

lemma slp_right_branch_output_append:
  "slp_right_branch_output (left @ right) terminal =
    slp_right_branch_output left 0 + slp_right_branch_output right terminal"
  by (simp add: slp_right_branch_output_def algebra_simps)

lemma slp_left_branch_output_eq_right:
  "slp_left_branch_output pairs terminal =
    slp_right_branch_output pairs terminal"
  by (simp add: slp_left_branch_output_def slp_right_branch_output_def)

lemma slp_mixed_branch_center_expansion:
  "slp_mixed_branch_center origin left_pairs left_terminal
      right_pairs right_terminal =
    - origin + left_terminal + sum_list (map slp_branch_increment left_pairs) +
      right_terminal + sum_list (map slp_branch_increment right_pairs)"
  by (simp add: slp_mixed_branch_center_def slp_left_branch_output_def
      slp_right_branch_output_def algebra_simps)

end
