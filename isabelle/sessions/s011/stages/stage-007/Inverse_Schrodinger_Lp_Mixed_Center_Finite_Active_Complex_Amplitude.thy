theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Active_Complex_Amplitude
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_007.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Active_Unpack_Measurable"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_005.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Complex_Amplitude"
begin

section \<open>Exact finite mixed amplitude on active Cartesian coordinates\<close>

definition slp_mixed_center_finite_active_complex_amplitude ::
    "(slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      slp_point \<Rightarrow>
      real^((unit + ((('i::finite + 'i) + unit) + ('j::finite + 'j)))
        \<times> bool) \<Rightarrow>
      complex"
where
  "slp_mixed_center_finite_active_complex_amplitude root_weight left_cutoff
      left_potential right_cutoff right_potential center x =
    slp_mixed_center_finite_complex_amplitude root_weight left_cutoff
      left_potential right_cutoff right_potential center
      (slp_mixed_center_finite_active_unpack x)"

theorem slp_mixed_center_finite_active_complex_amplitude_pack:
  fixes coordinates ::
    "('i::finite, 'j::finite) slp_mixed_center_finite_coordinates"
  shows
    "slp_mixed_center_finite_active_complex_amplitude root_weight left_cutoff
        left_potential right_cutoff right_potential center
        (slp_mixed_center_finite_active_pack coordinates) =
      slp_mixed_center_finite_complex_amplitude root_weight left_cutoff
        left_potential right_cutoff right_potential center coordinates"
  unfolding slp_mixed_center_finite_active_complex_amplitude_def
  by (simp only: slp_mixed_center_finite_active_unpack_pack)

end
