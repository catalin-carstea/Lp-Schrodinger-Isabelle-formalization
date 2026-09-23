theory Inverse_Schrodinger_Lp_Partial_Psi_Translation_Covariance
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_010.Inverse_Schrodinger_Lp_Smooth_Translation_Interface"
begin

section \<open>Translation covariance of the oscillatory partial-Cauchy operator\<close>

lemma slp_center_kernel_translate:
  "slp_center_kernel tau c (c + x) = slp_center_kernel tau 0 x"
proof -
  have phase_translate:
      "slp_center_phase c (c + x) = slp_center_phase 0 x"
    unfolding slp_center_phase_def
    by (simp add: algebra_simps)
  show ?thesis
    unfolding slp_center_kernel_def
    by (simp only: phase_translate)
qed

lemma slp_cauchy_kernel_translate:
  "slp_cauchy_kernel orientation (c + z) (c + y) =
    slp_cauchy_kernel orientation z y"
proof -
  have point_add:
      "slp_point_as_complex (u + v) =
        slp_point_as_complex u + slp_point_as_complex v" for u v
    by (rule complex_eqI)
      (simp_all only: slp_point_as_complex_def complex.sel
        vector_add_component plus_complex.sel)
  have point_difference:
      "slp_point_as_complex (c + z) -
          slp_point_as_complex (c + y) =
        slp_point_as_complex z - slp_point_as_complex y"
    by (simp only: point_add add_diff_cancel_left)
  have denominator_translate:
      "slp_cauchy_denominator orientation (c + z) (c + y) =
        slp_cauchy_denominator orientation z y"
    by (cases orientation)
      (simp_all only: slp_cauchy_denominator_def
        slp_cauchy_orientation.simps point_difference)
  show ?thesis
    unfolding slp_cauchy_kernel_def
    by (simp only: denominator_translate)
qed

lemma slp_partial_psi_inverse_translate:
  assumes f_test: "slp_test_function_on UNIV f"
  shows
    "slp_partial_psi_inverse tau c f (c + z) =
      slp_partial_psi_inverse tau 0 (\<lambda>x. f (c + x)) z"
proof -
  have source_test:
      "slp_test_function_on UNIV
        (slp_oscillatory_modulation tau c f)"
    unfolding slp_oscillatory_modulation_def
    by (rule slp_test_function_on_mult_left[
          OF slp_center_kernel_smooth f_test])
  have source_integrable_at:
      "slp_cauchy_integrable_at SLP_Partial_Inverse
        (slp_oscillatory_modulation tau c f) (c + z)"
    by (rule slp_test_function_cauchy_integrable_at[OF source_test])
  have source_integrable:
      "integrable lborel
        (slp_cauchy_integrand SLP_Partial_Inverse
          (slp_oscillatory_modulation tau c f) (c + z))"
    using source_integrable_at
    unfolding slp_cauchy_integrable_at_def .
  have translated_integral:
      "integral\<^sup>L lborel
          (slp_cauchy_integrand SLP_Partial_Inverse
            (slp_oscillatory_modulation tau c f) (c + z)) =
        integral\<^sup>L lborel
          (\<lambda>x. slp_cauchy_integrand SLP_Partial_Inverse
            (slp_oscillatory_modulation tau c f) (c + z) (c + x))"
    by (rule sym, rule slp_lborel_integral_translate[OF source_integrable])
  have integrand_translate:
      "(\<lambda>x. slp_cauchy_integrand SLP_Partial_Inverse
          (slp_oscillatory_modulation tau c f) (c + z) (c + x)) =
        slp_cauchy_integrand SLP_Partial_Inverse
          (slp_oscillatory_modulation tau 0 (\<lambda>x. f (c + x))) z"
  proof (rule ext)
    fix x :: slp_point
    show "slp_cauchy_integrand SLP_Partial_Inverse
          (slp_oscillatory_modulation tau c f) (c + z) (c + x) =
        slp_cauchy_integrand SLP_Partial_Inverse
          (slp_oscillatory_modulation tau 0 (\<lambda>x. f (c + x))) z x"
      unfolding slp_cauchy_integrand_def slp_oscillatory_modulation_def
      by (simp only: slp_center_kernel_translate
          slp_cauchy_kernel_translate)
  qed
  show ?thesis
    unfolding slp_partial_psi_inverse_eq slp_cauchy_transform_def
    using translated_integral
    by (simp only: integrand_translate)
qed

end
