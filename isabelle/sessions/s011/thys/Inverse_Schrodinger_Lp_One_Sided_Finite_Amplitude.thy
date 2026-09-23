theory Inverse_Schrodinger_Lp_One_Sided_Finite_Amplitude
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_One_Sided_Finite_Output"
begin

section \<open>The exact one-sided amplitude in finite manuscript coordinates\<close>

definition slp_left_branch_complex_amplitude_finite ::
    "(slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      'i::finite slp_left_branch_finite_coordinates \<Rightarrow> complex"
where
  "slp_left_branch_complex_amplitude_finite root_weight cutoff potential
      terminal_value output_factor coordinates =
    root_weight (fst coordinates) *
      slp_left_branch_complex_kernel_joint cutoff potential terminal_value
        coordinates *
      output_factor
        (slp_left_branch_output
          (slp_finite_branch_pair_list
            (\<lambda>i. fst (fst (snd coordinates)) $ i)
            (\<lambda>i. snd (fst (snd coordinates)) $ i))
          (snd (snd coordinates)))"

theorem slp_left_branch_complex_amplitude_packed_finite:
  fixes coordinates :: "'i::finite slp_left_branch_finite_coordinates"
  shows
    "slp_left_branch_complex_amplitude_packed root_weight cutoff potential
        terminal_value output_factor
        (fst (slp_one_sided_finite_to_packed_coordinates coordinates))
        (snd (slp_one_sided_finite_to_packed_coordinates coordinates)) =
      slp_left_branch_complex_amplitude_finite root_weight cutoff potential
        terminal_value output_factor coordinates"
proof -
  have root_identity:
      "slp_complex_as_point
          (slp_complex_coordinate_unpack
            (fst (slp_one_sided_finite_to_packed_coordinates coordinates))) =
        fst coordinates"
    unfolding slp_one_sided_finite_to_packed_coordinates_def Let_def
    by (simp only: fst_conv snd_conv slp_complex_coordinate_unpack_pack
        slp_complex_as_point_point_as_complex)
  have coordinate_inverse:
      "slp_one_sided_packed_to_finite_coordinates
          (slp_one_sided_finite_to_packed_coordinates coordinates) =
        coordinates"
    by (rule slp_one_sided_finite_to_packed_to_finite)
  have output_identity:
      "slp_one_sided_packed_output_point
          (snd (slp_one_sided_finite_to_packed_coordinates coordinates)) =
        slp_left_branch_output
          (slp_finite_branch_pair_list
            (\<lambda>i. fst (fst (snd coordinates)) $ i)
            (\<lambda>i. snd (fst (snd coordinates)) $ i))
          (snd (snd coordinates))"
    by (rule slp_one_sided_finite_packed_output_point)
  show ?thesis
    unfolding slp_left_branch_complex_amplitude_packed_def
      slp_left_branch_complex_amplitude_finite_def
      slp_left_branch_complex_kernel_packed_def
    by (simp only: root_identity coordinate_inverse output_identity
        prod.collapse)
qed

end
