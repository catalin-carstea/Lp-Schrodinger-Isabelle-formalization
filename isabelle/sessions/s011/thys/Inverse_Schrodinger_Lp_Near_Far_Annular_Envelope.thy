theory Inverse_Schrodinger_Lp_Near_Far_Annular_Envelope
  imports Inverse_Schrodinger_Lp_Far_Annular_Tau_Scaling
begin

section \<open>The complete near--far scalar envelope\<close>

lemma slp_near_far_annular_inverse_sqrt_bound:
  assumes tau_positive: "0 < tau"
    and normalized_lower: "1 \<le> R * sqrt tau"
    and L_nonnegative: "0 \<le> L"
    and f_measurable: "f \<in> borel_measurable lborel"
    and M_nonnegative: "0 \<le> M"
    and f_bound: "\<And>y. norm (f y) \<le> M"
  shows "slp_localized_riesz_potential
        (2 * inverse (sqrt tau)) f z +
      (1 / tau) *
        (((L * sqrt tau) * M *
              (integral\<^sup>L lborel
                  (slp_annular_I1_integrand (inverse (sqrt tau)) z) +
                integral\<^sup>L lborel
                  (slp_annular_I2_integrand (inverse (sqrt tau)) z)) +
            M * integral\<^sup>L lborel
              (slp_annular_J1_full_integrand
                (inverse (sqrt tau)) R z)) +
          M * integral\<^sup>L lborel
            (slp_annular_J2_full_integrand
              (inverse (sqrt tau)) R z)) \<le>
    inverse (sqrt tau) *
      (((2 * M + (3 * L + 1) * M) *
          integral\<^sup>L lborel (slp_localized_cauchy_kernel 1)) +
        M * (1 + log 2 (R * sqrt tau)) *
          integral\<^sup>L lborel (slp_squared_radial_annulus 1 2))"
proof -
  have delta_positive: "0 < inverse (sqrt tau)"
    using tau_positive by simp
  note near = slp_near_center_envelope_bound[OF
      delta_positive f_measurable M_nonnegative f_bound,
      where z = z]
  note far = slp_full_annular_far_tau_scaled_bound[OF
      tau_positive normalized_lower L_nonnegative M_nonnegative,
      where z = z]
  have combined:
    "slp_localized_riesz_potential
          (2 * inverse (sqrt tau)) f z +
        (1 / tau) *
          (((L * sqrt tau) * M *
                (integral\<^sup>L lborel
                    (slp_annular_I1_integrand (inverse (sqrt tau)) z) +
                  integral\<^sup>L lborel
                    (slp_annular_I2_integrand (inverse (sqrt tau)) z)) +
              M * integral\<^sup>L lborel
                (slp_annular_J1_full_integrand
                  (inverse (sqrt tau)) R z)) +
            M * integral\<^sup>L lborel
              (slp_annular_J2_full_integrand
                (inverse (sqrt tau)) R z)) \<le>
      2 * inverse (sqrt tau) * M *
          integral\<^sup>L lborel (slp_localized_cauchy_kernel 1) +
        inverse (sqrt tau) *
          ((((3 * L + 1) * M) *
              integral\<^sup>L lborel (slp_localized_cauchy_kernel 1)) +
            M * (1 + log 2 (R * sqrt tau)) *
              integral\<^sup>L lborel (slp_squared_radial_annulus 1 2))"
    by (rule add_mono[OF near far])
  show ?thesis
    using combined by (simp add: algebra_simps)
qed

end
