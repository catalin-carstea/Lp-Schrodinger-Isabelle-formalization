theory Inverse_Schrodinger_Lp_Right_One_Sided_Finite_Principal_Decay
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Right_Finite_Residual_Decay"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Right_One_Sided_Finite_Principal_Integral"
begin

section \<open>Decay of the direct right principal finite integral\<close>

theorem slp_right_branch_principal_finite_integral_decay:
  fixes branch_dummy :: "'i::finite itself"
  assumes stationary_phase:
      "hormander_quadratic_stationary_phase_decay_claim
        TYPE(('i + 'i) \<times> bool)"
    and density:
      "evans_compact_smooth_l1_density_claim TYPE(('i + 'i) \<times> bool)"
    and root_weight_measurable:
      "root_weight \<in> borel_measurable lborel"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_measurable: "potential \<in> borel_measurable lborel"
    and terminal_value_measurable:
      "terminal_value \<in> borel_measurable lborel"
    and test_measurable: "test \<in> borel_measurable lborel"
    and terminal_test_amplitude_integrable:
      "integrable lborel
        (slp_right_branch_complex_amplitude_finite root_weight cutoff potential
          terminal_value test ::
          'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
    and unit_source_amplitude_integrable:
      "integrable lborel
        (slp_right_branch_complex_amplitude_finite root_weight cutoff potential
          (\<lambda>_. 1) (\<lambda>u. test u * terminal_value u) ::
          'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
  shows
    "((\<lambda>omega. slp_right_branch_principal_finite_integral TYPE('i)
        omega root_weight cutoff potential terminal_value test)
      \<longlongrightarrow> 0) at_top"
proof -
  have source_measurable:
      "(\<lambda>u. test u * terminal_value u) \<in> borel_measurable lborel"
    using test_measurable terminal_value_measurable by measurable
  have terminal_decay:
      "((\<lambda>omega.
          slp_right_branch_finite_oscillatory_integral TYPE('i) omega
            root_weight cutoff potential terminal_value test)
        \<longlongrightarrow> 0) at_top"
    unfolding slp_right_branch_finite_oscillatory_integral_def
    by (rule slp_right_branch_complex_amplitude_finite_residual_decay[OF
          stationary_phase density root_weight_measurable cutoff_measurable
          potential_measurable terminal_value_measurable test_measurable
          terminal_test_amplitude_integrable])
  have output_decay:
      "((\<lambda>omega.
          slp_right_branch_finite_oscillatory_integral TYPE('i) omega
            root_weight cutoff potential (\<lambda>_. 1)
              (\<lambda>u. test u * terminal_value u))
        \<longlongrightarrow> 0) at_top"
    unfolding slp_right_branch_finite_oscillatory_integral_def
    by (rule slp_right_branch_complex_amplitude_finite_residual_decay[OF
          stationary_phase density root_weight_measurable cutoff_measurable
          potential_measurable _ source_measurable
          unit_source_amplitude_integrable]) measurable
  have principal_eq:
      "(\<lambda>omega. slp_right_branch_principal_finite_integral TYPE('i)
          omega root_weight cutoff potential terminal_value test) =
        (\<lambda>omega.
          slp_right_branch_finite_oscillatory_integral TYPE('i) omega
              root_weight cutoff potential terminal_value test -
            slp_right_branch_finite_oscillatory_integral TYPE('i) omega
              root_weight cutoff potential (\<lambda>_. 1)
                (\<lambda>u. test u * terminal_value u))"
    by (rule ext)
      (rule slp_right_branch_principal_finite_integral_eq_base_pair[OF
        terminal_test_amplitude_integrable unit_source_amplitude_integrable])
  have difference_decay:
      "((\<lambda>omega.
          slp_right_branch_finite_oscillatory_integral TYPE('i) omega
              root_weight cutoff potential terminal_value test -
            slp_right_branch_finite_oscillatory_integral TYPE('i) omega
              root_weight cutoff potential (\<lambda>_. 1)
                (\<lambda>u. test u * terminal_value u))
        \<longlongrightarrow> 0 - 0) at_top"
    by (rule tendsto_diff[OF terminal_decay output_decay])
  show ?thesis
    unfolding principal_eq
    using difference_decay by simp
qed

end
