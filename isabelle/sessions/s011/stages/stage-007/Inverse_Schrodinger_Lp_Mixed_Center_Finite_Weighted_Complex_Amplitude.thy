theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Complex_Amplitude
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_005.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Complex_Amplitude"
begin

section \<open>Terminal- and center-weighted finite mixed amplitude\<close>

definition slp_mixed_center_finite_weighted_complex_amplitude ::
    "(slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      slp_point \<Rightarrow>
      ('i::finite, 'j::finite) slp_mixed_center_finite_coordinates \<Rightarrow>
      complex"
where
  "slp_mixed_center_finite_weighted_complex_amplitude root_weight
      left_cutoff left_potential left_terminal_value right_cutoff
      right_potential right_terminal_value center_factor center coordinates =
    root_weight (fst coordinates) *
      slp_left_branch_complex_kernel_joint left_cutoff left_potential
        left_terminal_value
        (fst (slp_mixed_center_finite_inserted_coordinates
          center coordinates)) *
      slp_right_branch_complex_kernel_joint right_cutoff right_potential
        right_terminal_value
        (snd (slp_mixed_center_finite_inserted_coordinates
          center coordinates)) *
      center_factor center"

theorem slp_mixed_center_finite_weighted_complex_amplitude_unit:
  fixes coordinates ::
    "('i::finite, 'j::finite) slp_mixed_center_finite_coordinates"
  shows
    "slp_mixed_center_finite_weighted_complex_amplitude root_weight
        left_cutoff left_potential (\<lambda>_. 1) right_cutoff
        right_potential (\<lambda>_. 1) (\<lambda>_. 1) center coordinates =
      slp_mixed_center_finite_complex_amplitude root_weight left_cutoff
        left_potential right_cutoff right_potential center coordinates"
  unfolding slp_mixed_center_finite_weighted_complex_amplitude_def
    slp_mixed_center_finite_complex_amplitude_def
  by simp

end
