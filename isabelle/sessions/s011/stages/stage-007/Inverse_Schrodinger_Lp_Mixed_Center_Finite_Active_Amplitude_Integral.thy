theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Active_Amplitude_Integral
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_007.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Active_Amplitude_Fiber_Integrable"
begin

section \<open>Exact active-coordinate amplitude integral\<close>

theorem slp_mixed_center_finite_active_complex_amplitude_integral:
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
        (slp_mixed_center_finite_active_complex_amplitude root_weight
          left_cutoff left_potential right_cutoff right_potential center ::
          real^((unit + ((('i::finite + 'i) + unit) + ('j::finite + 'j)))
            \<times> bool) \<Rightarrow> complex) =
      integral\<^sup>L lborel
        (slp_mixed_center_finite_complex_amplitude root_weight left_cutoff
          left_potential right_cutoff right_potential center ::
          ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
proof -
  have active_measurable:
      "(slp_mixed_center_finite_active_complex_amplitude root_weight
          left_cutoff left_potential right_cutoff right_potential center ::
        real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool)
          \<Rightarrow> complex) \<in>
        borel_measurable lborel"
    by (rule
          slp_mixed_center_finite_active_complex_amplitude_measurable[OF
            root_weight_measurable left_cutoff_measurable
            left_potential_measurable right_cutoff_measurable
            right_potential_measurable])
  note transported = slp_mixed_center_finite_active_integral[
    OF active_measurable]
  show ?thesis
    using transported
    by (simp only: slp_mixed_center_finite_active_complex_amplitude_pack)
qed

end
