theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Positive_Weight
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_007.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Complex_Amplitude_Measurable"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_006.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Positive_Weight"
begin

section \<open>Positive weight of the terminal- and center-weighted amplitude\<close>

theorem slp_right_branch_complex_kernel_joint_positive_weight:
  fixes R :: real
    and coordinates ::
      "'i::finite slp_left_branch_finite_coordinates"
  assumes chain:
    "slp_left_branch_radius_chain_joint R coordinates"
  shows
    "ennreal (cmod (slp_right_branch_complex_kernel_joint cutoff potential
        terminal_value coordinates)) =
      slp_left_branch_positive_kernel_joint R cutoff potential terminal_value
        coordinates"
proof -
  have positive_list_conjugate:
      "slp_left_branch_positive_kernel_list R
          (\<lambda>x. cnj (cutoff x))
          (\<lambda>x. cnj (potential x))
          (\<lambda>x. cnj (terminal_value x)) pairs origin terminal =
        slp_left_branch_positive_kernel_list R cutoff potential terminal_value
          pairs origin terminal"
    for pairs origin terminal
  proof (induction pairs arbitrary: origin)
    case Nil
    then show ?case by simp
  next
    case (Cons pair pairs)
    then show ?case
      by (simp add: slp_positive_branch_block_weight_def)
  qed
  have positive_joint_conjugate:
      "slp_left_branch_positive_kernel_joint R
          (\<lambda>x. cnj (cutoff x))
          (\<lambda>x. cnj (potential x))
          (\<lambda>x. cnj (terminal_value x)) coordinates =
        slp_left_branch_positive_kernel_joint R cutoff potential terminal_value
          coordinates"
    unfolding slp_left_branch_positive_kernel_joint_def
      slp_left_branch_positive_kernel_finite_def
    by (rule positive_list_conjugate)
  have conjugated_kernel:
      "ennreal (cmod (slp_left_branch_complex_kernel_joint
          (\<lambda>x. cnj (cutoff x))
          (\<lambda>x. cnj (potential x))
          (\<lambda>x. cnj (terminal_value x)) coordinates)) =
        slp_left_branch_positive_kernel_joint R
          (\<lambda>x. cnj (cutoff x))
          (\<lambda>x. cnj (potential x))
          (\<lambda>x. cnj (terminal_value x)) coordinates"
    by (rule slp_left_branch_complex_kernel_joint_positive_weight[OF chain])
  show ?thesis
    unfolding slp_right_branch_complex_kernel_joint_def
    using conjugated_kernel positive_joint_conjugate
    by simp
qed

theorem slp_mixed_center_finite_weighted_complex_amplitude_positive_weight:
  fixes R :: real
    and root_weight left_cutoff left_potential left_terminal_value
      right_cutoff right_potential right_terminal_value center_factor ::
      "slp_point \<Rightarrow> complex"
    and center :: slp_point
    and coordinates ::
      "('i::finite, 'j::finite) slp_mixed_center_finite_coordinates"
  assumes left_chain:
      "slp_left_branch_radius_chain_joint R
        (fst (slp_mixed_center_finite_inserted_coordinates
          center coordinates))"
    and right_chain:
      "slp_left_branch_radius_chain_joint R
        (snd (slp_mixed_center_finite_inserted_coordinates
          center coordinates))"
  shows
    "ennreal (cmod
        (slp_mixed_center_finite_weighted_complex_amplitude root_weight
          left_cutoff left_potential left_terminal_value right_cutoff
          right_potential right_terminal_value center_factor center
          coordinates)) =
      ennreal (cmod (root_weight (fst coordinates))) *
        slp_left_branch_positive_kernel_joint R left_cutoff left_potential
          left_terminal_value
          (fst (slp_mixed_center_finite_inserted_coordinates
            center coordinates)) *
        slp_left_branch_positive_kernel_joint R right_cutoff right_potential
          right_terminal_value
          (snd (slp_mixed_center_finite_inserted_coordinates
            center coordinates)) *
        ennreal (cmod (center_factor center))"
proof -
  have left_kernel:
      "ennreal (cmod (slp_left_branch_complex_kernel_joint left_cutoff
          left_potential left_terminal_value
          (fst (slp_mixed_center_finite_inserted_coordinates
            center coordinates)))) =
        slp_left_branch_positive_kernel_joint R left_cutoff left_potential
          left_terminal_value
          (fst (slp_mixed_center_finite_inserted_coordinates
            center coordinates))"
    by (rule slp_left_branch_complex_kernel_joint_positive_weight[OF
          left_chain])
  have right_kernel:
      "ennreal (cmod (slp_right_branch_complex_kernel_joint right_cutoff
          right_potential right_terminal_value
          (snd (slp_mixed_center_finite_inserted_coordinates
            center coordinates)))) =
        slp_left_branch_positive_kernel_joint R right_cutoff right_potential
          right_terminal_value
          (snd (slp_mixed_center_finite_inserted_coordinates
            center coordinates))"
    by (rule slp_right_branch_complex_kernel_joint_positive_weight[OF
          right_chain])
  show ?thesis
    unfolding slp_mixed_center_finite_weighted_complex_amplitude_def
    by (simp add: norm_mult ennreal_mult left_kernel right_kernel)
qed

end
