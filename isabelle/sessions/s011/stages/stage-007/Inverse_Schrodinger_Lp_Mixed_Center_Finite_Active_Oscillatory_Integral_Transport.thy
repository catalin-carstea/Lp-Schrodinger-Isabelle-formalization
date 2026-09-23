theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Active_Oscillatory_Integral_Transport
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_007.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Active_Integral_Transport"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_007.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Active_Oscillatory_Integrand"
begin

section \<open>Exact oscillatory-integral transport to finite coordinates\<close>

theorem slp_mixed_center_finite_active_oscillatory_integral:
  assumes root_weight_measurable:
      "root_weight \<in> borel_measurable lborel"
    and left_cutoff_measurable:
      "left_cutoff \<in> borel_measurable lborel"
    and left_potential_measurable:
      "left_potential \<in> borel_measurable lborel"
    and right_cutoff_measurable:
      "right_cutoff \<in> borel_measurable lborel"
    and right_potential_measurable:
      "right_potential \<in> borel_measurable lborel"
  shows
    "integral\<^sup>L lborel
        (slp_mixed_center_finite_active_oscillatory_integrand frequency
          root_weight left_cutoff left_potential right_cutoff right_potential
          center ::
          real^((unit + ((('i::finite + 'i) + unit) +
            ('j::finite + 'j))) \<times> bool) \<Rightarrow> complex) =
      integral\<^sup>L lborel
        (slp_mixed_center_finite_oscillatory_integrand frequency root_weight
          left_cutoff left_potential right_cutoff right_potential center ::
          ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
proof -
  have integrand_measurable:
      "(slp_mixed_center_finite_active_oscillatory_integrand frequency
          root_weight left_cutoff left_potential right_cutoff right_potential
          center ::
        real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool)
          \<Rightarrow> complex) \<in>
        borel_measurable lborel"
    by (rule
          slp_mixed_center_finite_active_oscillatory_integrand_measurable[OF
            root_weight_measurable left_cutoff_measurable
            left_potential_measurable right_cutoff_measurable
            right_potential_measurable])
  have transported:
      "integral\<^sup>L lborel
          (slp_mixed_center_finite_active_oscillatory_integrand frequency
            root_weight left_cutoff left_potential right_cutoff
            right_potential center ::
            real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool)
              \<Rightarrow> complex) =
        integral\<^sup>L lborel
          (\<lambda>coordinates ::
            ('i, 'j) slp_mixed_center_finite_coordinates.
            slp_mixed_center_finite_active_oscillatory_integrand frequency
              root_weight left_cutoff left_potential right_cutoff
              right_potential center
              (slp_mixed_center_finite_active_pack coordinates))"
    by (rule slp_mixed_center_finite_active_integral[OF
          integrand_measurable])
  show ?thesis
    using transported
    by (simp only:
          slp_mixed_center_finite_active_oscillatory_integrand_pack)
qed

end
