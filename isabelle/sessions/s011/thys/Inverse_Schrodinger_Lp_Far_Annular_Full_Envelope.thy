theory Inverse_Schrodinger_Lp_Far_Annular_Full_Envelope
  imports Inverse_Schrodinger_Lp_Annular_J2_Full_Bounds
begin

section \<open>The complete checked full-annulus scalar envelope\<close>

lemma slp_full_annular_far_weighted_logarithmic_bound:
  assumes delta_positive: "0 < delta"
    and normalized_lower: "1 \<le> R / delta"
    and L_nonnegative: "0 \<le> L"
    and M_nonnegative: "0 \<le> M"
  shows "((L / delta) * M *
          (integral\<^sup>L lborel (slp_annular_I1_integrand delta z) +
            integral\<^sup>L lborel (slp_annular_I2_integrand delta z)) +
        M * integral\<^sup>L lborel
          (slp_annular_J1_full_integrand delta R z)) +
      M * integral\<^sup>L lborel
        (slp_annular_J2_full_integrand delta R z) \<le>
    ((3 * L + 1) * M / delta) *
        integral\<^sup>L lborel (slp_localized_cauchy_kernel 1) +
      (M / delta) * (1 + log 2 (R / delta)) *
        integral\<^sup>L lborel (slp_squared_radial_annulus 1 2)"
proof -
  have near_output:
    "(L / delta) * M *
          (integral\<^sup>L lborel (slp_annular_I1_integrand delta z) +
            integral\<^sup>L lborel (slp_annular_I2_integrand delta z)) +
        M * integral\<^sup>L lborel
          (slp_annular_J1_full_integrand delta R z) \<le>
      ((3 * L + 1) * M / delta) *
        integral\<^sup>L lborel (slp_localized_cauchy_kernel 1)"
    by (rule slp_checked_annular_weighted_sum_full_J1_bound[OF
          delta_positive L_nonnegative M_nonnegative])
  have complementary:
    "M * integral\<^sup>L lborel
        (slp_annular_J2_full_integrand delta R z) \<le>
      (M / delta) * (1 + log 2 (R / delta)) *
        integral\<^sup>L lborel (slp_squared_radial_annulus 1 2)"
    by (rule slp_J2_full_amplitude_weighted_logarithmic_bound[OF
          delta_positive normalized_lower M_nonnegative])
  show ?thesis
    by (rule add_mono[OF near_output complementary])
qed

end
