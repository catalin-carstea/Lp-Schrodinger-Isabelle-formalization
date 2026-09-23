theory Inverse_Schrodinger_Lp_Right_Graph_Finite_Primitive_Difference
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Right_Graph_Finite_Modulation"
begin

section \<open>Finite right primitive-difference graph factorization\<close>

lemma slp_right_branch_complex_amplitude_finite_terminal_diff:
  fixes coordinates :: "'i::finite slp_left_branch_finite_coordinates"
    and scalar :: complex
  shows
    "slp_right_branch_complex_amplitude_finite root_weight cutoff potential
        (\<lambda>x. terminal_value x - scalar) output_factor coordinates =
      slp_right_branch_complex_amplitude_finite root_weight cutoff potential
          terminal_value output_factor coordinates -
        scalar *
          slp_right_branch_complex_amplitude_finite root_weight cutoff potential
            (\<lambda>_. 1) output_factor coordinates"
  unfolding slp_right_branch_complex_amplitude_finite_def
    slp_right_branch_complex_kernel_joint_def
    slp_left_branch_complex_kernel_joint_def
    slp_left_branch_complex_kernel_finite_def
  apply (simp only: complex_cnj_diff complex_cnj_cnj)
  apply (subst slp_left_branch_complex_kernel_list_terminal_diff)
  by (simp add: algebra_simps)

theorem
    slp_right_branch_oscillatory_graph_kernel_fixed_root_finite_primitive_diff:
  fixes coordinates :: "'i::finite slp_left_branch_finite_coordinates"
    and primitive :: "slp_point \<Rightarrow> complex"
  shows
    "root_weight (fst coordinates) *
        slp_right_branch_oscillatory_graph_kernel_fixed_root_finite tau center
          cutoff potential (\<lambda>x. primitive x - primitive center)
          (fst coordinates) (snd coordinates) =
      slp_center_kernel tau center
          (slp_right_branch_output
            (slp_finite_branch_pair_list
              (\<lambda>i. fst (fst (snd coordinates)) $ i)
              (\<lambda>i. snd (fst (snd coordinates)) $ i))
            (snd (snd coordinates))) *
        (exp (\<i> * of_real
            (tau * slp_one_sided_finite_residual coordinates)) *
            slp_right_branch_complex_amplitude_finite root_weight cutoff
              potential primitive (\<lambda>_. 1) coordinates -
          primitive center *
            (exp (\<i> * of_real
                (tau * slp_one_sided_finite_residual coordinates)) *
              slp_right_branch_complex_amplitude_finite root_weight cutoff
                potential (\<lambda>_. 1) (\<lambda>_. 1) coordinates))"
proof -
  note modulation =
    slp_right_branch_oscillatory_graph_kernel_fixed_root_finite_modulation[
      where coordinates = coordinates and tau = tau and center = center
        and root_weight = root_weight and cutoff = cutoff
        and potential = potential
        and terminal_value = "\<lambda>x. primitive x - primitive center"]
  have amplitude_diff:
      "slp_right_branch_complex_amplitude_finite root_weight cutoff potential
          (\<lambda>x. primitive x - primitive center) (\<lambda>_. 1)
          coordinates =
        slp_right_branch_complex_amplitude_finite root_weight cutoff potential
            primitive (\<lambda>_. 1) coordinates -
          primitive center *
            slp_right_branch_complex_amplitude_finite root_weight cutoff
              potential (\<lambda>_. 1) (\<lambda>_. 1) coordinates"
    by (rule slp_right_branch_complex_amplitude_finite_terminal_diff)
  show ?thesis
    apply (subst modulation)
    apply (subst amplitude_diff)
    by (simp only: right_diff_distrib mult.assoc mult.left_commute
        mult.commute)
qed

end
