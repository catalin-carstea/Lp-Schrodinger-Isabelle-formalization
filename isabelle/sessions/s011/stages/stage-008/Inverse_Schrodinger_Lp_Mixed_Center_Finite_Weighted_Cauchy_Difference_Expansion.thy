theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Cauchy_Difference_Expansion
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_008.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Oscillatory_Unit_Unit_Global_Decay"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_003.Inverse_Schrodinger_Lp_Left_Graph_Natural_Primitive_Difference_Integrable"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Exact four-placement expansion of the primitive differences\<close>

lemma slp_left_branch_complex_kernel_joint_terminal_diff:
  fixes coordinates :: "'i::finite slp_left_branch_finite_coordinates"
    and scalar :: complex
  shows
    "slp_left_branch_complex_kernel_joint cutoff potential
        (\<lambda>x. terminal_value x - scalar) coordinates =
      slp_left_branch_complex_kernel_joint cutoff potential terminal_value
          coordinates -
        scalar * slp_left_branch_complex_kernel_joint cutoff potential
          (\<lambda>_. 1) coordinates"
  unfolding slp_left_branch_complex_kernel_joint_def
    slp_left_branch_complex_kernel_finite_def
  by (rule slp_left_branch_complex_kernel_list_terminal_diff)

lemma slp_right_branch_complex_kernel_joint_terminal_diff:
  fixes coordinates :: "'i::finite slp_left_branch_finite_coordinates"
    and scalar :: complex
  shows
    "slp_right_branch_complex_kernel_joint cutoff potential
        (\<lambda>x. terminal_value x - scalar) coordinates =
      slp_right_branch_complex_kernel_joint cutoff potential terminal_value
          coordinates -
        scalar * slp_right_branch_complex_kernel_joint cutoff potential
          (\<lambda>_. 1) coordinates"
  unfolding slp_right_branch_complex_kernel_joint_def
    slp_left_branch_complex_kernel_joint_def
    slp_left_branch_complex_kernel_finite_def
  apply (simp only: complex_cnj_diff complex_cnj_cnj)
  apply (subst slp_left_branch_complex_kernel_list_terminal_diff)
  by (simp add: algebra_simps)

theorem slp_mixed_center_finite_weighted_complex_amplitude_cauchy_center_diff_expansion:
  fixes center :: slp_point
    and coordinates ::
      "('i::finite, 'j::finite) slp_mixed_center_finite_coordinates"
  shows
    "slp_mixed_center_finite_weighted_complex_amplitude root_weight
        left_cutoff left_potential
        (\<lambda>x. left_terminal x - left_terminal center)
        right_cutoff right_potential
        (\<lambda>x. right_terminal x - right_terminal center)
        center_factor center coordinates =
      slp_mixed_center_finite_weighted_complex_amplitude root_weight
          left_cutoff left_potential left_terminal right_cutoff
          right_potential right_terminal center_factor center coordinates +
      slp_mixed_center_finite_weighted_complex_amplitude root_weight
          left_cutoff left_potential left_terminal right_cutoff
          right_potential (\<lambda>_. 1)
          (\<lambda>x. -(center_factor x * right_terminal x))
          center coordinates +
      slp_mixed_center_finite_weighted_complex_amplitude root_weight
          left_cutoff left_potential (\<lambda>_. 1) right_cutoff
          right_potential right_terminal
          (\<lambda>x. -(center_factor x * left_terminal x))
          center coordinates +
      slp_mixed_center_finite_weighted_complex_amplitude root_weight
          left_cutoff left_potential (\<lambda>_. 1) right_cutoff
          right_potential (\<lambda>_. 1)
          (\<lambda>x. center_factor x *
            (left_terminal x * right_terminal x))
          center coordinates"
  unfolding slp_mixed_center_finite_weighted_complex_amplitude_def
  apply (simp only:
      slp_left_branch_complex_kernel_joint_terminal_diff
      slp_right_branch_complex_kernel_joint_terminal_diff)
  by (simp add: algebra_simps)

theorem slp_mixed_center_finite_weighted_oscillatory_integrand_cauchy_center_diff_expansion:
  fixes center :: slp_point
    and coordinates ::
      "('i::finite, 'j::finite) slp_mixed_center_finite_coordinates"
  shows
    "slp_mixed_center_finite_weighted_oscillatory_integrand frequency
        root_weight left_cutoff left_potential
        (\<lambda>x. left_terminal x - left_terminal center)
        right_cutoff right_potential
        (\<lambda>x. right_terminal x - right_terminal center)
        center_factor center coordinates =
      slp_mixed_center_finite_weighted_oscillatory_integrand frequency
          root_weight left_cutoff left_potential left_terminal right_cutoff
          right_potential right_terminal center_factor center coordinates +
      slp_mixed_center_finite_weighted_oscillatory_integrand frequency
          root_weight left_cutoff left_potential left_terminal right_cutoff
          right_potential (\<lambda>_. 1)
          (\<lambda>x. -(center_factor x * right_terminal x))
          center coordinates +
      slp_mixed_center_finite_weighted_oscillatory_integrand frequency
          root_weight left_cutoff left_potential (\<lambda>_. 1) right_cutoff
          right_potential right_terminal
          (\<lambda>x. -(center_factor x * left_terminal x))
          center coordinates +
      slp_mixed_center_finite_weighted_oscillatory_integrand frequency
          root_weight left_cutoff left_potential (\<lambda>_. 1) right_cutoff
          right_potential (\<lambda>_. 1)
          (\<lambda>x. center_factor x *
            (left_terminal x * right_terminal x))
          center coordinates"
  unfolding slp_mixed_center_finite_weighted_oscillatory_integrand_def
    slp_parameterized_real_phase_integrand_def
  apply (simp only:
      slp_mixed_center_finite_weighted_complex_amplitude_cauchy_center_diff_expansion)
  by (simp add: algebra_simps)

end
