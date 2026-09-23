theory Inverse_Schrodinger_Lp_Right_Graph_Finite_Amplitude_Conjugate
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Right_Graph_Finite_Modulation"
begin

section \<open>Conjugation and integrability of finite right amplitudes\<close>

lemma slp_right_branch_complex_amplitude_finite_conjugate:
  fixes coordinates :: "'i::finite slp_left_branch_finite_coordinates"
  shows
    "slp_right_branch_complex_amplitude_finite root_weight cutoff potential
        terminal_value output_factor coordinates =
      cnj (slp_left_branch_complex_amplitude_finite
        (\<lambda>x. cnj (root_weight x)) (\<lambda>x. cnj (cutoff x))
        (\<lambda>x. cnj (potential x)) (\<lambda>x. cnj (terminal_value x))
        (\<lambda>x. cnj (output_factor x)) coordinates)"
  unfolding slp_right_branch_complex_amplitude_finite_def
    slp_right_branch_complex_kernel_joint_def
    slp_left_branch_complex_amplitude_finite_def
  by (simp add: slp_left_branch_output_eq_right algebra_simps)

lemma slp_right_branch_complex_amplitude_finite_norm [simp]:
  fixes coordinates :: "'i::finite slp_left_branch_finite_coordinates"
  shows
    "cmod (slp_right_branch_complex_amplitude_finite root_weight cutoff
        potential terminal_value output_factor coordinates) =
      cmod (slp_left_branch_complex_amplitude_finite
        (\<lambda>x. cnj (root_weight x)) (\<lambda>x. cnj (cutoff x))
        (\<lambda>x. cnj (potential x)) (\<lambda>x. cnj (terminal_value x))
        (\<lambda>x. cnj (output_factor x)) coordinates)"
  by (simp only: slp_right_branch_complex_amplitude_finite_conjugate
      complex_mod_cnj)

theorem slp_right_branch_complex_amplitude_finite_integrable_iff:
  "integrable M
      (slp_right_branch_complex_amplitude_finite root_weight cutoff potential
        terminal_value output_factor ::
          'i::finite slp_left_branch_finite_coordinates \<Rightarrow> complex)
    \<longleftrightarrow>
    integrable M
      (slp_left_branch_complex_amplitude_finite
        (\<lambda>x. cnj (root_weight x)) (\<lambda>x. cnj (cutoff x))
        (\<lambda>x. cnj (potential x)) (\<lambda>x. cnj (terminal_value x))
        (\<lambda>x. cnj (output_factor x)) ::
          'i slp_left_branch_finite_coordinates \<Rightarrow> complex)"
proof -
  let ?left =
    "slp_left_branch_complex_amplitude_finite
      (\<lambda>x. cnj (root_weight x)) (\<lambda>x. cnj (cutoff x))
      (\<lambda>x. cnj (potential x)) (\<lambda>x. cnj (terminal_value x))
      (\<lambda>x. cnj (output_factor x)) ::
        'i slp_left_branch_finite_coordinates \<Rightarrow> complex"
  have right_eq:
      "(slp_right_branch_complex_amplitude_finite root_weight cutoff potential
          terminal_value output_factor ::
            'i slp_left_branch_finite_coordinates \<Rightarrow> complex) =
        (\<lambda>coordinates. cnj (?left coordinates))"
    by (rule ext)
      (rule slp_right_branch_complex_amplitude_finite_conjugate)
  show ?thesis
    unfolding right_eq
  proof
    assume right_integrable:
        "integrable M (\<lambda>coordinates. cnj (?left coordinates))"
    have twice_integrable:
        "integrable M (\<lambda>coordinates. cnj (cnj (?left coordinates)))"
      by (rule integrable_cnj[OF right_integrable])
    show "integrable M ?left"
      using twice_integrable by simp
  next
    assume left_integrable: "integrable M ?left"
    show "integrable M (\<lambda>coordinates. cnj (?left coordinates))"
      by (rule integrable_cnj[OF left_integrable])
  qed
qed

end
