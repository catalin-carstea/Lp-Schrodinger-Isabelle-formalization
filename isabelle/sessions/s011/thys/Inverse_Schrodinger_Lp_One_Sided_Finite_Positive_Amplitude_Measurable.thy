theory Inverse_Schrodinger_Lp_One_Sided_Finite_Positive_Amplitude_Measurable
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_Left_Positive_Kernel_Finite_Measurable"
begin

section \<open>Measurability of the finite positive amplitude\<close>

lemma slp_left_branch_positive_amplitude_finite_factors:
  fixes coordinates :: "'i::finite slp_left_branch_finite_coordinates"
  shows
    "slp_left_branch_positive_amplitude_finite R root_weight cutoff potential
        terminal_value output_factor coordinates =
      ennreal (norm (root_weight (fst coordinates))) *
        slp_left_branch_positive_kernel_joint R cutoff potential terminal_value
          coordinates *
        ennreal (norm (output_factor
          (slp_one_sided_packed_output_point
            (snd (slp_one_sided_finite_to_packed_coordinates coordinates)))))"
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
  show ?thesis
    unfolding slp_left_branch_positive_amplitude_finite_def
      slp_left_branch_positive_amplitude_packed_def
      slp_left_branch_positive_kernel_packed_def
    by (simp only: split_beta prod.collapse root_identity coordinate_inverse)
qed

theorem slp_left_branch_positive_amplitude_finite_measurable:
  fixes branch_dummy :: "'i::finite itself"
  assumes root_weight_measurable:
      "root_weight \<in> borel_measurable lborel"
    and cutoff_measurable:
      "cutoff \<in> borel_measurable lborel"
    and potential_measurable:
      "potential \<in> borel_measurable lborel"
    and terminal_value_measurable:
      "terminal_value \<in> borel_measurable lborel"
    and output_factor_measurable:
      "output_factor \<in> borel_measurable lborel"
  shows
    "(slp_left_branch_positive_amplitude_finite R root_weight cutoff potential
        terminal_value output_factor ::
      'i slp_left_branch_finite_coordinates \<Rightarrow> ennreal)
      \<in> borel_measurable lborel"
proof -
  have root_coordinate_measurable:
      "(\<lambda>coordinates :: 'i slp_left_branch_finite_coordinates.
        fst coordinates) \<in> measurable lborel lborel"
    apply (simp only: measurable_lborel1 measurable_lborel2)
    by (rule borel_measurable_continuous_onI) (intro continuous_intros)
  have root_value_measurable[measurable]:
      "(\<lambda>coordinates :: 'i slp_left_branch_finite_coordinates.
        root_weight (fst coordinates)) \<in> borel_measurable lborel"
    using measurable_comp[OF root_coordinate_measurable
      root_weight_measurable]
    by (simp only: comp_def)
  have packed_coordinates_measurable:
      "(slp_one_sided_finite_to_packed_coordinates ::
        'i slp_left_branch_finite_coordinates \<Rightarrow>
          (real^bool) \<times>
            (real^((unit + ('i + 'i)) \<times> bool)))
        \<in> measurable lborel (lborel \<Otimes>\<^sub>M lborel)"
    by (rule slp_one_sided_finite_to_packed_coordinates_measurable)
  have branch_coordinate_measurable:
      "(\<lambda>coordinates :: 'i slp_left_branch_finite_coordinates.
        snd (slp_one_sided_finite_to_packed_coordinates coordinates))
        \<in> measurable lborel lborel"
    using packed_coordinates_measurable by measurable
  have output_point_measurable[measurable]:
      "(\<lambda>coordinates :: 'i slp_left_branch_finite_coordinates.
        slp_one_sided_packed_output_point
          (snd (slp_one_sided_finite_to_packed_coordinates coordinates)))
        \<in> borel_measurable lborel"
    using measurable_comp[OF branch_coordinate_measurable
      slp_one_sided_packed_output_point_measurable]
    by (simp only: comp_def)
  have output_value_measurable[measurable]:
      "(\<lambda>coordinates :: 'i slp_left_branch_finite_coordinates.
        output_factor (slp_one_sided_packed_output_point
          (snd (slp_one_sided_finite_to_packed_coordinates coordinates))))
        \<in> borel_measurable lborel"
  proof -
    have output_point_lborel:
        "(\<lambda>coordinates :: 'i slp_left_branch_finite_coordinates.
          slp_one_sided_packed_output_point
            (snd (slp_one_sided_finite_to_packed_coordinates coordinates)))
          \<in> measurable lborel lborel"
      using output_point_measurable by (simp only: measurable_lborel1)
    show ?thesis
      using measurable_comp[OF output_point_lborel output_factor_measurable]
    by (simp only: comp_def)
  qed
  have kernel_measurable[measurable]:
      "(slp_left_branch_positive_kernel_joint R cutoff potential
          terminal_value ::
        'i slp_left_branch_finite_coordinates \<Rightarrow> ennreal)
        \<in> borel_measurable lborel"
    by (rule slp_left_branch_positive_kernel_joint_measurable[OF
          cutoff_measurable potential_measurable terminal_value_measurable])
  have amplitude_equality:
      "(slp_left_branch_positive_amplitude_finite R root_weight cutoff
          potential terminal_value output_factor ::
        'i slp_left_branch_finite_coordinates \<Rightarrow> ennreal) =
        (\<lambda>coordinates.
          ennreal (norm (root_weight (fst coordinates))) *
            slp_left_branch_positive_kernel_joint R cutoff potential
              terminal_value coordinates *
            ennreal (norm (output_factor
              (slp_one_sided_packed_output_point
                (snd (slp_one_sided_finite_to_packed_coordinates
                  coordinates))))))"
    by (rule ext) (rule slp_left_branch_positive_amplitude_finite_factors)
  show ?thesis
    unfolding amplitude_equality
    by measurable
qed

end
