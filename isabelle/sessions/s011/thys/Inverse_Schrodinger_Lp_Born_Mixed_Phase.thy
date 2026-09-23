theory Inverse_Schrodinger_Lp_Born_Mixed_Phase
  imports Inverse_Schrodinger_Lp_Born_Branch_Phase
begin

section \<open>Mixed Born hierarchical phase splitting\<close>

definition slp_mixed_core_residual ::
    "slp_point \<Rightarrow> slp_point \<Rightarrow> slp_point \<Rightarrow> real" where
  "slp_mixed_core_residual origin left_output right_output =
    - slp_point_quadratic_value origin +
      slp_point_quadratic_value left_output +
      slp_point_quadratic_value right_output -
      slp_point_quadratic_value (- origin + left_output + right_output)"

definition slp_mixed_branch_phase ::
    "slp_point \<Rightarrow> slp_point \<Rightarrow>
      (slp_point \<times> slp_point) list \<Rightarrow> slp_point \<Rightarrow>
      (slp_point \<times> slp_point) list \<Rightarrow> slp_point \<Rightarrow> real" where
  "slp_mixed_branch_phase center origin left_pairs left_terminal
      right_pairs right_terminal =
    - slp_center_phase center origin +
      slp_left_branch_phase center left_pairs left_terminal +
      slp_right_branch_phase center right_pairs right_terminal"

definition slp_mixed_branch_residual ::
    "slp_point \<Rightarrow>
      (slp_point \<times> slp_point) list \<Rightarrow> slp_point \<Rightarrow>
      (slp_point \<times> slp_point) list \<Rightarrow> slp_point \<Rightarrow> real" where
  "slp_mixed_branch_residual origin left_pairs left_terminal
      right_pairs right_terminal =
    slp_left_branch_residual left_pairs left_terminal +
      slp_right_branch_residual right_pairs right_terminal +
      slp_mixed_core_residual origin
        (slp_left_branch_output left_pairs left_terminal)
        (slp_right_branch_output right_pairs right_terminal)"

lemma slp_mixed_core_phase_split:
  "- slp_center_phase center origin + slp_center_phase center left_output +
      slp_center_phase center right_output =
    slp_center_phase center (- origin + left_output + right_output) +
      slp_mixed_core_residual origin left_output right_output"
  unfolding slp_center_phase_def slp_point_quadratic_value_def
    slp_mixed_core_residual_def
  by (simp add: power2_eq_square algebra_simps)

theorem slp_mixed_branch_phase_split:
  "slp_mixed_branch_phase center origin left_pairs left_terminal
      right_pairs right_terminal =
    slp_center_phase center
      (slp_mixed_branch_center origin left_pairs left_terminal
        right_pairs right_terminal) +
    slp_mixed_branch_residual origin left_pairs left_terminal
      right_pairs right_terminal"
proof -
  let ?left = "slp_left_branch_output left_pairs left_terminal"
  let ?right = "slp_right_branch_output right_pairs right_terminal"
  have left_split:
      "slp_left_branch_phase center left_pairs left_terminal =
        slp_center_phase center ?left +
          slp_left_branch_residual left_pairs left_terminal"
    by (rule slp_left_branch_phase_split)
  have right_split:
      "slp_right_branch_phase center right_pairs right_terminal =
        slp_center_phase center ?right +
          slp_right_branch_residual right_pairs right_terminal"
    by (rule slp_right_branch_phase_split)
  have core_split:
      "- slp_center_phase center origin + slp_center_phase center ?left +
          slp_center_phase center ?right =
        slp_center_phase center (- origin + ?left + ?right) +
          slp_mixed_core_residual origin ?left ?right"
    by (rule slp_mixed_core_phase_split)
  show ?thesis
    using left_split right_split core_split
    by (simp add: slp_mixed_branch_phase_def
        slp_mixed_branch_center_def slp_mixed_branch_residual_def
        algebra_simps)
qed

end
