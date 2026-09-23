theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Active_Oscillatory_Integrand
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_007.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Active_Amplitude_Integral"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_005.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Oscillatory_Integrand"
begin

section \<open>Exact oscillatory integrand on active Cartesian coordinates\<close>

definition slp_mixed_center_finite_active_oscillatory_integrand ::
    "real \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      slp_point \<Rightarrow>
      real^((unit + ((('i::finite + 'i) + unit) + ('j::finite + 'j)))
        \<times> bool) \<Rightarrow>
      complex"
where
  "slp_mixed_center_finite_active_oscillatory_integrand frequency root_weight
      left_cutoff left_potential right_cutoff right_potential center x =
    slp_parameterized_real_phase_integrand frequency
      slp_mixed_center_finite_active_residual
      (slp_mixed_center_finite_active_complex_amplitude root_weight
        left_cutoff left_potential right_cutoff right_potential)
      center x"

theorem slp_mixed_center_finite_active_oscillatory_integrand_pack:
  fixes coordinates ::
    "('i::finite, 'j::finite) slp_mixed_center_finite_coordinates"
  shows
    "slp_mixed_center_finite_active_oscillatory_integrand frequency
        root_weight left_cutoff left_potential right_cutoff right_potential
        center (slp_mixed_center_finite_active_pack coordinates) =
      slp_mixed_center_finite_oscillatory_integrand frequency root_weight
        left_cutoff left_potential right_cutoff right_potential center
        coordinates"
  unfolding slp_mixed_center_finite_active_oscillatory_integrand_def
    slp_mixed_center_finite_oscillatory_integrand_def
    slp_parameterized_real_phase_integrand_def
  by (simp only: slp_mixed_center_finite_active_residual_pack
      slp_mixed_center_finite_active_complex_amplitude_pack)

theorem slp_mixed_center_finite_active_oscillatory_integrand_measurable:
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
    "(slp_mixed_center_finite_active_oscillatory_integrand frequency
        root_weight left_cutoff left_potential right_cutoff right_potential
        center ::
      real^((unit + ((('i::finite + 'i) + unit) + ('j::finite + 'j)))
        \<times> bool) \<Rightarrow> complex) \<in>
      borel_measurable lborel"
proof -
  have phase_measurable:
      "(slp_mixed_center_finite_active_residual center ::
        real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool)
          \<Rightarrow> real) \<in>
        borel_measurable lborel"
    by (rule slp_mixed_center_finite_active_residual_measurable)
  have amplitude_measurable:
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
  show ?thesis
    unfolding slp_mixed_center_finite_active_oscillatory_integrand_def
      slp_parameterized_real_phase_integrand_def
    using phase_measurable amplitude_measurable by measurable
qed

end
