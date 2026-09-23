theory Inverse_Schrodinger_Lp_Positive_Kernel_Joint_Fixed_Output_Integral
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_006.Inverse_Schrodinger_Lp_Positive_Kernel_Finite_Fixed_Output_Integral"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_Left_Complex_Kernel_Packed_Weight"
begin

section \<open>Joint positive kernels at a prescribed output\<close>

theorem slp_left_branch_positive_kernel_joint_fixed_output_integral:
  fixes branch_dummy :: "'i::finite itself"
  assumes cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and potential_measurable[measurable]:
      "potential \<in> borel_measurable lborel"
    and terminal_value_measurable[measurable]:
      "terminal_value \<in> borel_measurable lborel"
  shows
    "nn_integral
        (lborel :: ((slp_point^'i) \<times> (slp_point^'i)) measure)
        (\<lambda>(pos, neg).
          slp_left_branch_positive_kernel_joint R cutoff potential
            terminal_value
            (origin, ((pos, neg),
              target - slp_left_branch_output
                (slp_finite_branch_pair_list (($) pos) (($) neg)) 0))) =
      slp_positive_output_density R cutoff potential
        (\<lambda>x. ennreal (norm (terminal_value x))) CARD('i) origin target"
proof -
  note finite =
    slp_left_branch_positive_kernel_finite_fixed_output_integral[
      where R = R and cutoff = cutoff and potential = potential
        and terminal_value = terminal_value
        and origin = origin and target = target,
      OF cutoff_measurable potential_measurable terminal_value_measurable]
  show ?thesis
    using finite
    unfolding slp_left_branch_positive_kernel_joint_def
      slp_left_branch_positive_kernel_finite_def
      slp_left_branch_positive_kernel_list_fixed_output_def
    by (simp only: split_beta' fst_conv snd_conv)
qed

end
