theory Inverse_Schrodinger_Lp_Born_Phase_Modulation
  imports Inverse_Schrodinger_Lp_Born_Mixed_Phase
begin

section \<open>Output-center modulation of finite Born phases\<close>

definition slp_left_branch_residual_oscillation ::
    "real \<Rightarrow> (slp_point \<times> slp_point) list \<Rightarrow>
      slp_point \<Rightarrow> complex" where
  "slp_left_branch_residual_oscillation tau pairs terminal =
    exp (\<i> * of_real (tau * slp_left_branch_residual pairs terminal))"

definition slp_right_branch_residual_oscillation ::
    "real \<Rightarrow> (slp_point \<times> slp_point) list \<Rightarrow>
      slp_point \<Rightarrow> complex" where
  "slp_right_branch_residual_oscillation tau pairs terminal =
    exp (\<i> * of_real (tau * slp_right_branch_residual pairs terminal))"

definition slp_mixed_branch_residual_oscillation ::
    "real \<Rightarrow> slp_point \<Rightarrow>
      (slp_point \<times> slp_point) list \<Rightarrow> slp_point \<Rightarrow>
      (slp_point \<times> slp_point) list \<Rightarrow> slp_point \<Rightarrow> complex" where
  "slp_mixed_branch_residual_oscillation tau origin left_pairs left_terminal
      right_pairs right_terminal =
    exp (\<i> * of_real (tau *
      slp_mixed_branch_residual origin left_pairs left_terminal
        right_pairs right_terminal))"

theorem slp_left_branch_phase_modulation:
  "exp (\<i> * of_real (tau *
      slp_left_branch_phase center pairs terminal)) =
    slp_center_kernel tau center
      (slp_left_branch_output pairs terminal) *
    slp_left_branch_residual_oscillation tau pairs terminal"
  using slp_left_branch_phase_split[of center pairs terminal]
  unfolding slp_center_kernel_def slp_left_branch_residual_oscillation_def
  by (simp add: exp_add algebra_simps)

theorem slp_right_branch_phase_modulation:
  "exp (\<i> * of_real (tau *
      slp_right_branch_phase center pairs terminal)) =
    slp_center_kernel tau center
      (slp_right_branch_output pairs terminal) *
    slp_right_branch_residual_oscillation tau pairs terminal"
  using slp_right_branch_phase_split[of center pairs terminal]
  unfolding slp_center_kernel_def slp_right_branch_residual_oscillation_def
  by (simp add: exp_add algebra_simps)

theorem slp_mixed_branch_phase_modulation:
  "exp (\<i> * of_real (tau *
      slp_mixed_branch_phase center origin left_pairs left_terminal
        right_pairs right_terminal)) =
    slp_center_kernel tau center
      (slp_mixed_branch_center origin left_pairs left_terminal
        right_pairs right_terminal) *
    slp_mixed_branch_residual_oscillation tau origin left_pairs left_terminal
      right_pairs right_terminal"
  using slp_mixed_branch_phase_split[of center origin left_pairs left_terminal
      right_pairs right_terminal]
  unfolding slp_center_kernel_def slp_mixed_branch_residual_oscillation_def
  by (simp add: exp_add algebra_simps)

lemma slp_left_branch_residual_oscillation_norm [simp]:
  "norm (slp_left_branch_residual_oscillation tau pairs terminal) = 1"
  unfolding slp_left_branch_residual_oscillation_def
  by (simp only: norm_exp_i_times)

lemma slp_right_branch_residual_oscillation_norm [simp]:
  "norm (slp_right_branch_residual_oscillation tau pairs terminal) = 1"
  unfolding slp_right_branch_residual_oscillation_def
  by (simp only: norm_exp_i_times)

lemma slp_mixed_branch_residual_oscillation_norm [simp]:
  "norm (slp_mixed_branch_residual_oscillation tau origin left_pairs
      left_terminal right_pairs right_terminal) = 1"
  unfolding slp_mixed_branch_residual_oscillation_def
  by (simp only: norm_exp_i_times)

end
