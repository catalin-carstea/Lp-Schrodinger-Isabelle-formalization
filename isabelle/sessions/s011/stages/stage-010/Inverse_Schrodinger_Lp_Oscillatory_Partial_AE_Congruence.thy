theory Inverse_Schrodinger_Lp_Oscillatory_Partial_AE_Congruence
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_010.Inverse_Schrodinger_Lp_Qstar_Centered_Three_Term_Source_HLS"
begin

section \<open>Almost-everywhere congruence of the oscillatory partial-Cauchy operator\<close>

lemma slp_partial_psi_inverse_cong_AE:
  assumes f_measurable: "f \<in> borel_measurable lborel"
    and g_measurable: "g \<in> borel_measurable lborel"
    and source_eq: "AE y in (lborel :: slp_point measure). f y = g y"
  shows "slp_partial_psi_inverse tau c f =
    slp_partial_psi_inverse tau c g"
proof (rule ext)
  fix z :: slp_point
  have modulated_eq:
      "AE y in (lborel :: slp_point measure).
        slp_oscillatory_modulation tau c f y =
          slp_oscillatory_modulation tau c g y"
    using source_eq
    by eventually_elim (simp add: slp_oscillatory_modulation_def)
  have f_modulated_measurable:
      "slp_oscillatory_modulation tau c f \<in> borel_measurable lborel"
    by (rule slp_oscillatory_modulation_measurable[OF f_measurable])
  have g_modulated_measurable:
      "slp_oscillatory_modulation tau c g \<in> borel_measurable lborel"
    by (rule slp_oscillatory_modulation_measurable[OF g_measurable])
  have f_integrand_measurable:
      "slp_cauchy_integrand SLP_Partial_Inverse
          (slp_oscillatory_modulation tau c f) z
        \<in> borel_measurable lborel"
    by (rule slp_cauchy_integrand_borel_measurable[
          OF f_modulated_measurable])
  have g_integrand_measurable:
      "slp_cauchy_integrand SLP_Partial_Inverse
          (slp_oscillatory_modulation tau c g) z
        \<in> borel_measurable lborel"
    by (rule slp_cauchy_integrand_borel_measurable[
          OF g_modulated_measurable])
  have integrands_eq:
      "AE y in (lborel :: slp_point measure).
        slp_cauchy_integrand SLP_Partial_Inverse
            (slp_oscillatory_modulation tau c f) z y =
          slp_cauchy_integrand SLP_Partial_Inverse
            (slp_oscillatory_modulation tau c g) z y"
    using modulated_eq
    by eventually_elim (simp add: slp_cauchy_integrand_def)
  have integral_eq:
      "integral\<^sup>L lborel
          (slp_cauchy_integrand SLP_Partial_Inverse
            (slp_oscillatory_modulation tau c f) z) =
        integral\<^sup>L lborel
          (slp_cauchy_integrand SLP_Partial_Inverse
            (slp_oscillatory_modulation tau c g) z)"
    by (rule integral_cong_AE[
          OF f_integrand_measurable g_integrand_measurable integrands_eq])
  show "slp_partial_psi_inverse tau c f z =
      slp_partial_psi_inverse tau c g z"
    unfolding slp_partial_psi_inverse_def slp_cauchy_transform_def
    using integral_eq by simp
qed

end
