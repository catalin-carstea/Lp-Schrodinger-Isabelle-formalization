theory Inverse_Schrodinger_Lp_Qstar_Centered_Annular_Representation
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_010.Inverse_Schrodinger_Lp_Qstar_Cutoff_Partial_Complex_Lp"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_010.Inverse_Schrodinger_Lp_Qstar_Square_Denominator_Complex_Lp"
begin

section \<open>Centered annular source representations\<close>

definition slp_qstar_centered_cutoff_partial_source ::
  "real \<Rightarrow> slp_scalar_field \<Rightarrow> slp_scalar_field"
where
  "slp_qstar_centered_cutoff_partial_source delta f y =
    slp_real_wirtinger_partial
      (slp_global_cutoff.slp_scaled_cutoff_derivative delta 0 y) *
    inverse (slp_point_as_complex y) * f y"

definition slp_qstar_centered_square_denominator_source ::
  "real \<Rightarrow> slp_scalar_field \<Rightarrow> slp_scalar_field"
where
  "slp_qstar_centered_square_denominator_source delta f y =
    of_real (1 - slp_global_cutoff.slp_scaled_cutoff delta 0 y) *
    inverse (slp_point_as_complex y) ^ 2 * f y"

theorem slp_qstar_centered_cutoff_partial_representation:
  "slp_partial_psi_inverse tau 0
      (slp_qstar_centered_cutoff_partial_source delta f) z =
    inverse (of_real pi) *
      slp_qstar_cutoff_partial_integral delta
        (slp_oscillatory_modulation tau 0 f) z"
proof -
  have integrand_eq:
      "slp_cauchy_integrand SLP_Partial_Inverse
          (slp_oscillatory_modulation tau 0
            (slp_qstar_centered_cutoff_partial_source delta f)) z =
        slp_qstar_cutoff_partial_integrand delta
          (slp_oscillatory_modulation tau 0 f) z"
  proof (rule ext)
    fix y :: slp_point
    show "slp_cauchy_integrand SLP_Partial_Inverse
          (slp_oscillatory_modulation tau 0
            (slp_qstar_centered_cutoff_partial_source delta f)) z y =
        slp_qstar_cutoff_partial_integrand delta
          (slp_oscillatory_modulation tau 0 f) z y"
      unfolding slp_cauchy_integrand_def slp_oscillatory_modulation_def
        slp_qstar_centered_cutoff_partial_source_def
        slp_qstar_cutoff_partial_integrand_def
      by (simp only: ac_simps)
  qed
  show ?thesis
    unfolding slp_partial_psi_inverse_def slp_cauchy_transform_def
      slp_qstar_cutoff_partial_integral_def
    by (simp only: integrand_eq)
qed

theorem slp_qstar_centered_square_denominator_representation:
  "slp_partial_psi_inverse tau 0
      (slp_qstar_centered_square_denominator_source delta f) z =
    inverse (of_real pi) *
      slp_qstar_square_denominator_integral delta
        (slp_oscillatory_modulation tau 0 f) z"
proof -
  have integrand_eq:
      "slp_cauchy_integrand SLP_Partial_Inverse
          (slp_oscillatory_modulation tau 0
            (slp_qstar_centered_square_denominator_source delta f)) z =
        slp_qstar_square_denominator_integrand delta
          (slp_oscillatory_modulation tau 0 f) z"
  proof (rule ext)
    fix y :: slp_point
    show "slp_cauchy_integrand SLP_Partial_Inverse
          (slp_oscillatory_modulation tau 0
            (slp_qstar_centered_square_denominator_source delta f)) z y =
        slp_qstar_square_denominator_integrand delta
          (slp_oscillatory_modulation tau 0 f) z y"
      unfolding slp_cauchy_integrand_def slp_oscillatory_modulation_def
        slp_qstar_centered_square_denominator_source_def
        slp_qstar_square_denominator_integrand_def
      by (simp only: ac_simps)
  qed
  show ?thesis
    unfolding slp_partial_psi_inverse_def slp_cauchy_transform_def
      slp_qstar_square_denominator_integral_def
    by (simp only: integrand_eq)
qed

end
