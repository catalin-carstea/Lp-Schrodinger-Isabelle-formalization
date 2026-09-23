theory Inverse_Schrodinger_Lp_Right_Finite_Oscillatory_Conjugation
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Right_Graph_Finite_Center_Output"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Right_Graph_Finite_Amplitude_Conjugate"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_One_Sided_Finite_Oscillatory_Output_Bound"
begin

section \<open>Conjugation of finite right oscillatory integrals\<close>

theorem slp_right_branch_finite_oscillatory_integral_conjugate:
  fixes branch_dummy :: "'i::finite itself"
  shows
    "slp_right_branch_finite_oscillatory_integral TYPE('i) omega root_weight
        cutoff potential terminal_value output_factor =
      cnj (slp_left_branch_finite_oscillatory_integral TYPE('i) (- omega)
        (\<lambda>x. cnj (root_weight x)) (\<lambda>x. cnj (cutoff x))
        (\<lambda>x. cnj (potential x)) (\<lambda>x. cnj (terminal_value x))
        (\<lambda>x. cnj (output_factor x)))"
  unfolding slp_right_branch_finite_oscillatory_integral_def
    slp_left_branch_finite_oscillatory_integral_def
  apply (subst Bochner_Integration.integral_cnj[symmetric])
  apply (rule Bochner_Integration.integral_cong)
  apply (rule refl)
  apply (simp add: slp_right_branch_complex_amplitude_finite_conjugate
      exp_cnj algebra_simps)
  done

corollary slp_right_branch_finite_oscillatory_integral_norm:
  fixes branch_dummy :: "'i::finite itself"
  shows
    "cmod (slp_right_branch_finite_oscillatory_integral TYPE('i) omega
        root_weight cutoff potential terminal_value output_factor) =
      cmod (slp_left_branch_finite_oscillatory_integral TYPE('i) (- omega)
        (\<lambda>x. cnj (root_weight x)) (\<lambda>x. cnj (cutoff x))
        (\<lambda>x. cnj (potential x)) (\<lambda>x. cnj (terminal_value x))
        (\<lambda>x. cnj (output_factor x)))"
  by (simp only: slp_right_branch_finite_oscillatory_integral_conjugate
      complex_mod_cnj)

end
