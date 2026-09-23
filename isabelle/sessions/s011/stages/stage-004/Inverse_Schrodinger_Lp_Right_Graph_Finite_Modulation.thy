theory Inverse_Schrodinger_Lp_Right_Graph_Finite_Modulation
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Right_Graph_Natural_Finite_Pointwise"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Left_Graph_Finite_Modulation"
begin

section \<open>Direct positive-frequency modulation of the finite right graph\<close>

definition slp_right_branch_complex_kernel_joint ::
    "(slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      'i::finite slp_left_branch_finite_coordinates \<Rightarrow> complex"
where
  "slp_right_branch_complex_kernel_joint cutoff potential terminal_value
      coordinates =
    cnj (slp_left_branch_complex_kernel_joint
      (\<lambda>x. cnj (cutoff x)) (\<lambda>x. cnj (potential x))
      (\<lambda>x. cnj (terminal_value x)) coordinates)"

definition slp_right_branch_complex_amplitude_finite ::
    "(slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      'i::finite slp_left_branch_finite_coordinates \<Rightarrow> complex"
where
  "slp_right_branch_complex_amplitude_finite root_weight cutoff potential
      terminal_value output_factor coordinates =
    root_weight (fst coordinates) *
      slp_right_branch_complex_kernel_joint cutoff potential terminal_value
        coordinates *
      output_factor
        (slp_right_branch_output
          (slp_finite_branch_pair_list
            (\<lambda>i. fst (fst (snd coordinates)) $ i)
            (\<lambda>i. snd (fst (snd coordinates)) $ i))
          (snd (snd coordinates)))"

lemma slp_right_branch_oscillatory_graph_kernel_fixed_root_finite_direct:
  fixes branch_coordinates ::
    "((slp_point^'i::finite) \<times> (slp_point^'i)) \<times> slp_point"
  shows
    "slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau center
        cutoff potential terminal_value origin branch_coordinates =
      exp (\<i> * of_real
        (tau * slp_right_branch_phase center
          (slp_finite_branch_pair_list
            (\<lambda>i. fst (fst branch_coordinates) $ i)
            (\<lambda>i. snd (fst branch_coordinates) $ i))
          (snd branch_coordinates))) *
      slp_right_branch_complex_kernel_joint cutoff potential terminal_value
        (origin, branch_coordinates)"
  unfolding
    slp_right_branch_oscillatory_graph_kernel_fixed_root_finite_def
    slp_left_branch_oscillatory_graph_kernel_fixed_root_finite_def
    slp_left_branch_oscillatory_graph_kernel_def
    slp_right_branch_complex_kernel_joint_def
    slp_left_branch_complex_kernel_joint_def
    slp_left_branch_complex_kernel_finite_def
    slp_right_branch_phase_def slp_left_branch_phase_def
  by (simp add: exp_cnj algebra_simps)

theorem slp_right_branch_oscillatory_graph_kernel_fixed_root_finite_modulation:
  fixes coordinates :: "'i::finite slp_left_branch_finite_coordinates"
  shows
    "root_weight (fst coordinates) *
        slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau center
          cutoff potential terminal_value (fst coordinates)
          (snd coordinates) =
      slp_center_kernel tau center
          (slp_right_branch_output
            (slp_finite_branch_pair_list
              (\<lambda>i. fst (fst (snd coordinates)) $ i)
              (\<lambda>i. snd (fst (snd coordinates)) $ i))
            (snd (snd coordinates))) *
        (exp (\<i> * of_real
            (tau * slp_one_sided_finite_residual coordinates)) *
          slp_right_branch_complex_amplitude_finite root_weight cutoff
            potential terminal_value (\<lambda>_. 1) coordinates)"
proof -
  let ?pairs =
    "slp_finite_branch_pair_list
      (\<lambda>i. fst (fst (snd coordinates)) $ i)
      (\<lambda>i. snd (fst (snd coordinates)) $ i)"
  have residual_modulation:
      "slp_right_branch_residual_oscillation tau ?pairs
          (snd (snd coordinates)) =
        exp (\<i> * of_real
          (tau * slp_one_sided_finite_residual coordinates))"
    unfolding slp_right_branch_residual_oscillation_def
      slp_right_branch_residual_def slp_left_branch_residual_def
    by (simp only: slp_one_sided_finite_residual_eq_left_branch
        slp_left_branch_residual_def)
  have phase_modulation:
      "exp (\<i> * of_real
          (tau * slp_right_branch_phase center ?pairs
            (snd (snd coordinates)))) =
        slp_center_kernel tau center
            (slp_right_branch_output ?pairs (snd (snd coordinates))) *
          exp (\<i> * of_real
            (tau * slp_one_sided_finite_residual coordinates))"
    apply (subst slp_right_branch_phase_modulation)
    apply (subst residual_modulation)
    by (rule refl)
  show ?thesis
    apply (subst
      slp_right_branch_oscillatory_graph_kernel_fixed_root_finite_direct)
    unfolding slp_right_branch_complex_amplitude_finite_def
    by (simp only: fst_conv snd_conv prod.collapse phase_modulation mult_1
        mult.assoc mult.left_commute mult.commute)
qed

end
