theory Inverse_Schrodinger_Lp_Far_Annular_Parameter_Choice
  imports Inverse_Schrodinger_Lp_Far_Annular_Full_Envelope
begin

section \<open>The inverse-square-root far-field parameter choice\<close>

lemma slp_full_annular_far_inverse_sqrt_parameter_bound:
  assumes tau_positive: "0 < tau"
    and normalized_lower: "1 \<le> R * sqrt tau"
    and L_nonnegative: "0 \<le> L"
    and M_nonnegative: "0 \<le> M"
  shows "((L * sqrt tau) * M *
          (integral\<^sup>L lborel
              (slp_annular_I1_integrand (inverse (sqrt tau)) z) +
            integral\<^sup>L lborel
              (slp_annular_I2_integrand (inverse (sqrt tau)) z)) +
        M * integral\<^sup>L lborel
          (slp_annular_J1_full_integrand
            (inverse (sqrt tau)) R z)) +
      M * integral\<^sup>L lborel
        (slp_annular_J2_full_integrand
          (inverse (sqrt tau)) R z) \<le>
    (((3 * L + 1) * M) * sqrt tau) *
        integral\<^sup>L lborel (slp_localized_cauchy_kernel 1) +
      (M * sqrt tau) * (1 + log 2 (R * sqrt tau)) *
        integral\<^sup>L lborel (slp_squared_radial_annulus 1 2)"
proof -
  have delta_positive: "0 < inverse (sqrt tau)"
    using tau_positive by simp
  have ratio_lower: "1 \<le> R / inverse (sqrt tau)"
    using normalized_lower by (simp add: divide_inverse)
  note envelope =
    slp_full_annular_far_weighted_logarithmic_bound[OF
      delta_positive ratio_lower L_nonnegative M_nonnegative,
      where z = z]
  show ?thesis
    using envelope by (simp add: divide_inverse)
qed

end
