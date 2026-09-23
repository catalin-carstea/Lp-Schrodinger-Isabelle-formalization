theory Inverse_Schrodinger_Lp_Left_Graph_Finite_Modulation
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Left_Graph_Natural_Finite_Integral"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_One_Sided_Finite_Residual_Identity"
begin

section \<open>Finite graph modulation by output and residual phase\<close>

theorem slp_left_branch_oscillatory_graph_kernel_fixed_root_finite_modulation:
  fixes coordinates :: "'i::finite slp_left_branch_finite_coordinates"
  shows
    "root_weight (fst coordinates) *
        slp_left_branch_oscillatory_graph_kernel_fixed_root_finite tau center
          cutoff potential terminal_value (fst coordinates)
          (snd coordinates) =
      slp_center_kernel tau center
          (slp_left_branch_output
            (slp_finite_branch_pair_list
              (\<lambda>i. fst (fst (snd coordinates)) $ i)
              (\<lambda>i. snd (fst (snd coordinates)) $ i))
            (snd (snd coordinates))) *
        (exp (\<i> * of_real
            (tau * slp_one_sided_finite_residual coordinates)) *
          slp_left_branch_complex_amplitude_finite root_weight cutoff
            potential terminal_value (\<lambda>_. 1) coordinates)"
proof -
  let ?pairs =
    "slp_finite_branch_pair_list
      (\<lambda>i. fst (fst (snd coordinates)) $ i)
      (\<lambda>i. snd (fst (snd coordinates)) $ i)"
  have residual_modulation:
      "slp_left_branch_residual_oscillation tau ?pairs
          (snd (snd coordinates)) =
        exp (\<i> * of_real
          (tau * slp_one_sided_finite_residual coordinates))"
    unfolding slp_left_branch_residual_oscillation_def
    apply (subst slp_one_sided_finite_residual_eq_left_branch)
    by (rule refl)
  have phase_modulation:
      "exp (\<i> * of_real
          (tau * slp_left_branch_phase center ?pairs
            (snd (snd coordinates)))) =
        slp_center_kernel tau center
            (slp_left_branch_output ?pairs (snd (snd coordinates))) *
          exp (\<i> * of_real
            (tau * slp_one_sided_finite_residual coordinates))"
    apply (subst slp_left_branch_phase_modulation)
    apply (subst residual_modulation)
    by (rule refl)
  show ?thesis
    unfolding
      slp_left_branch_oscillatory_graph_kernel_fixed_root_finite_def
      slp_left_branch_oscillatory_graph_kernel_def
      slp_left_branch_complex_amplitude_finite_def
      slp_left_branch_complex_kernel_joint_def
      slp_left_branch_complex_kernel_finite_def
    by (simp only: fst_conv snd_conv phase_modulation mult_1
        mult.assoc mult.left_commute mult.commute)
qed

end
