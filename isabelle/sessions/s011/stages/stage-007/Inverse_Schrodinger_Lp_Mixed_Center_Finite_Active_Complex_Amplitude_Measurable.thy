theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Active_Complex_Amplitude_Measurable
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_007.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Active_Complex_Amplitude"
begin

section \<open>Measurability of the active finite mixed amplitude\<close>

theorem slp_mixed_center_finite_active_complex_amplitude_measurable:
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
    "(slp_mixed_center_finite_active_complex_amplitude root_weight
        left_cutoff left_potential right_cutoff right_potential center ::
      real^((unit + ((('i::finite + 'i) + unit) + ('j::finite + 'j)))
        \<times> bool) \<Rightarrow> complex) \<in>
      borel_measurable lborel"
proof -
  let ?A =
    "lborel ::
      (real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool))
        measure"
  let ?F =
    "lborel :: (('i, 'j) slp_mixed_center_finite_coordinates) measure"
  let ?C = "lborel :: slp_point measure"
  let ?P =
    "lborel ::
      (slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates)
        measure"
  have amplitude_measurable:
      "((\<lambda>z ::
          slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
        slp_mixed_center_finite_complex_amplitude root_weight left_cutoff
          left_potential right_cutoff right_potential (fst z) (snd z)))
        \<in> borel_measurable ?P"
    by (rule slp_mixed_center_finite_complex_amplitude_measurable[OF
          root_weight_measurable left_cutoff_measurable
          left_potential_measurable right_cutoff_measurable
          right_potential_measurable])
  have center_in_space: "center \<in> space ?C"
    by (simp only: space_lborel space_borel UNIV_I)
  have center_measurable:
      "(\<lambda>_ ::
          real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool).
        center) \<in> measurable ?A ?C"
    by (rule measurable_const[OF center_in_space])
  have unpack_measurable:
      "(slp_mixed_center_finite_active_unpack ::
        real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool)
          \<Rightarrow> ('i, 'j) slp_mixed_center_finite_coordinates)
        \<in> measurable ?A ?F"
    by (rule slp_mixed_center_finite_active_unpack_measurable)
  have pair_measurable:
      "(\<lambda>x ::
          real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool).
        (center, slp_mixed_center_finite_active_unpack x)) \<in>
        measurable ?A ?P"
    using measurable_Pair[OF center_measurable unpack_measurable]
    by (simp only: lborel_prod)
  have composed:
      "((\<lambda>z ::
          slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates.
        slp_mixed_center_finite_complex_amplitude root_weight left_cutoff
          left_potential right_cutoff right_potential (fst z) (snd z)) \<circ>
        (\<lambda>x ::
          real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool).
          (center, slp_mixed_center_finite_active_unpack x))) \<in>
        borel_measurable ?A"
    using measurable_comp[OF pair_measurable amplitude_measurable]
    by (simp only: comp_def)
  show ?thesis
    using composed
    unfolding slp_mixed_center_finite_active_complex_amplitude_def comp_def
    by (simp only: fst_conv snd_conv)
qed

end
