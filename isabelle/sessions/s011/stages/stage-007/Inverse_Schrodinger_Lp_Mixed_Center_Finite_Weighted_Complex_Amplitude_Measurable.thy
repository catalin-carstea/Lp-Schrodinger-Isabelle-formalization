theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Complex_Amplitude_Measurable
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_007.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Complex_Amplitude"
begin

section \<open>Measurability of the weighted finite mixed amplitude\<close>

theorem slp_right_branch_complex_kernel_joint_measurable:
  assumes cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and potential_measurable[measurable]:
      "potential \<in> borel_measurable lborel"
    and terminal_value_measurable[measurable]:
      "terminal_value \<in> borel_measurable lborel"
  shows
    "(slp_right_branch_complex_kernel_joint cutoff potential terminal_value ::
      'i::finite slp_left_branch_finite_coordinates \<Rightarrow> complex)
      \<in> borel_measurable lborel"
proof -
  have cnj_measurable: "cnj \<in> borel_measurable borel"
    by (rule borel_measurable_continuous_onI) (intro continuous_intros)
  have conjugate_cutoff_measurable[measurable]:
      "(\<lambda>x. cnj (cutoff x)) \<in> borel_measurable lborel"
    using measurable_comp[OF cutoff_measurable cnj_measurable]
    by (simp only: comp_def)
  have conjugate_potential_measurable[measurable]:
      "(\<lambda>x. cnj (potential x)) \<in> borel_measurable lborel"
    using measurable_comp[OF potential_measurable cnj_measurable]
    by (simp only: comp_def)
  have conjugate_terminal_measurable[measurable]:
      "(\<lambda>x. cnj (terminal_value x)) \<in> borel_measurable lborel"
    using measurable_comp[OF terminal_value_measurable cnj_measurable]
    by (simp only: comp_def)
  have inner_measurable:
      "(slp_left_branch_complex_kernel_joint
          (\<lambda>x. cnj (cutoff x))
          (\<lambda>x. cnj (potential x))
          (\<lambda>x. cnj (terminal_value x)) ::
        'i slp_left_branch_finite_coordinates \<Rightarrow> complex)
        \<in> borel_measurable lborel"
    by (rule slp_left_branch_complex_kernel_joint_measurable[OF
          conjugate_cutoff_measurable conjugate_potential_measurable
          conjugate_terminal_measurable])
  show ?thesis
    unfolding slp_right_branch_complex_kernel_joint_def
    using measurable_comp[OF inner_measurable cnj_measurable]
    by (simp only: comp_def)
qed

theorem slp_mixed_center_finite_weighted_complex_amplitude_measurable:
  assumes root_weight_measurable[measurable]:
      "root_weight \<in> borel_measurable lborel"
    and left_cutoff_measurable[measurable]:
      "left_cutoff \<in> borel_measurable lborel"
    and left_potential_measurable[measurable]:
      "left_potential \<in> borel_measurable lborel"
    and left_terminal_measurable[measurable]:
      "left_terminal_value \<in> borel_measurable lborel"
    and right_cutoff_measurable[measurable]:
      "right_cutoff \<in> borel_measurable lborel"
    and right_potential_measurable[measurable]:
      "right_potential \<in> borel_measurable lborel"
    and right_terminal_measurable[measurable]:
      "right_terminal_value \<in> borel_measurable lborel"
    and center_factor_measurable[measurable]:
      "center_factor \<in> borel_measurable lborel"
  shows
    "((\<lambda>z :: slp_point \<times>
        ('i::finite, 'j::finite) slp_mixed_center_finite_coordinates.
      slp_mixed_center_finite_weighted_complex_amplitude root_weight
        left_cutoff left_potential left_terminal_value right_cutoff
        right_potential right_terminal_value center_factor
        (fst z) (snd z))) \<in> borel_measurable lborel"
proof -
  have inserted_coordinates_measurable[measurable]:
      "((\<lambda>z :: slp_point \<times>
          ('i, 'j) slp_mixed_center_finite_coordinates.
        slp_mixed_center_finite_inserted_coordinates (fst z) (snd z)))
        \<in> borel_measurable lborel"
    by (rule slp_mixed_center_finite_inserted_coordinates_measurable)
  have inserted_product_measurable:
      "((\<lambda>z :: slp_point \<times>
          ('i, 'j) slp_mixed_center_finite_coordinates.
        slp_mixed_center_finite_inserted_coordinates (fst z) (snd z)))
        \<in> measurable lborel (lborel \<Otimes>\<^sub>M lborel)"
    using inserted_coordinates_measurable
    by (simp only: lborel_prod measurable_lborel1)
  have left_coordinates_measurable:
      "((\<lambda>z. fst (slp_mixed_center_finite_inserted_coordinates
          (fst z) (snd z))) ::
        (slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates) \<Rightarrow>
          'i slp_left_branch_finite_coordinates)
        \<in> borel_measurable lborel"
    using measurable_compose[OF inserted_product_measurable measurable_fst]
    by (simp add: comp_def measurable_lborel1)
  have right_coordinates_measurable:
      "((\<lambda>z. snd (slp_mixed_center_finite_inserted_coordinates
          (fst z) (snd z))) ::
        (slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates) \<Rightarrow>
          'j slp_left_branch_finite_coordinates)
        \<in> borel_measurable lborel"
    using measurable_compose[OF inserted_product_measurable measurable_snd]
    by (simp add: comp_def measurable_lborel1)
  have left_kernel_measurable[measurable]:
      "(slp_left_branch_complex_kernel_joint left_cutoff left_potential
          left_terminal_value ::
        'i slp_left_branch_finite_coordinates \<Rightarrow> complex)
        \<in> borel_measurable lborel"
    by (rule slp_left_branch_complex_kernel_joint_measurable[OF
          left_cutoff_measurable left_potential_measurable
          left_terminal_measurable])
  have right_kernel_measurable[measurable]:
      "(slp_right_branch_complex_kernel_joint right_cutoff right_potential
          right_terminal_value ::
        'j slp_left_branch_finite_coordinates \<Rightarrow> complex)
        \<in> borel_measurable lborel"
    by (rule slp_right_branch_complex_kernel_joint_measurable[OF
          right_cutoff_measurable right_potential_measurable
          right_terminal_measurable])
  have left_kernel_borel_measurable:
      "(slp_left_branch_complex_kernel_joint left_cutoff left_potential
          left_terminal_value ::
        'i slp_left_branch_finite_coordinates \<Rightarrow> complex)
        \<in> borel_measurable borel"
    using left_kernel_measurable by (simp only: measurable_lborel2)
  have right_kernel_borel_measurable:
      "(slp_right_branch_complex_kernel_joint right_cutoff right_potential
          right_terminal_value ::
        'j slp_left_branch_finite_coordinates \<Rightarrow> complex)
        \<in> borel_measurable borel"
    using right_kernel_measurable by (simp only: measurable_lborel2)
  have left_kernel_composed:
      "((\<lambda>z :: slp_point \<times>
          ('i, 'j) slp_mixed_center_finite_coordinates.
        slp_left_branch_complex_kernel_joint left_cutoff left_potential
          left_terminal_value
          (fst (slp_mixed_center_finite_inserted_coordinates
            (fst z) (snd z))))) \<in> borel_measurable lborel"
    using measurable_compose[OF left_coordinates_measurable
      left_kernel_borel_measurable]
    by (simp only: comp_def)
  have right_kernel_composed:
      "((\<lambda>z :: slp_point \<times>
          ('i, 'j) slp_mixed_center_finite_coordinates.
        slp_right_branch_complex_kernel_joint right_cutoff right_potential
          right_terminal_value
          (snd (slp_mixed_center_finite_inserted_coordinates
            (fst z) (snd z))))) \<in> borel_measurable lborel"
    using measurable_compose[OF right_coordinates_measurable
      right_kernel_borel_measurable]
    by (simp only: comp_def)
  have root_coordinates_measurable:
      "((\<lambda>z :: slp_point \<times>
          ('i, 'j) slp_mixed_center_finite_coordinates. fst (snd z)))
        \<in> borel_measurable lborel"
    apply (simp only: measurable_lborel2)
    by (rule borel_measurable_continuous_onI) (intro continuous_intros)
  have center_coordinates_measurable:
      "((\<lambda>z :: slp_point \<times>
          ('i, 'j) slp_mixed_center_finite_coordinates. fst z))
        \<in> borel_measurable lborel"
    apply (simp only: measurable_lborel2)
    by (rule borel_measurable_continuous_onI) (intro continuous_intros)
  have root_weight_borel_measurable:
      "root_weight \<in> borel_measurable borel"
    using root_weight_measurable by (simp only: measurable_lborel2)
  have center_factor_borel_measurable:
      "center_factor \<in> borel_measurable borel"
    using center_factor_measurable by (simp only: measurable_lborel2)
  have root_weight_composed:
      "((\<lambda>z :: slp_point \<times>
          ('i, 'j) slp_mixed_center_finite_coordinates.
        root_weight (fst (snd z)))) \<in> borel_measurable lborel"
    by (rule measurable_compose[OF root_coordinates_measurable
          root_weight_borel_measurable])
  have center_factor_composed:
      "((\<lambda>z :: slp_point \<times>
          ('i, 'j) slp_mixed_center_finite_coordinates.
        center_factor (fst z))) \<in> borel_measurable lborel"
    by (rule measurable_compose[OF center_coordinates_measurable
          center_factor_borel_measurable])
  have root_left_product_measurable:
      "((\<lambda>z :: slp_point \<times>
          ('i, 'j) slp_mixed_center_finite_coordinates.
        root_weight (fst (snd z)) *
          slp_left_branch_complex_kernel_joint left_cutoff left_potential
            left_terminal_value
            (fst (slp_mixed_center_finite_inserted_coordinates
              (fst z) (snd z))))) \<in> borel_measurable lborel"
    by (rule borel_measurable_times[OF root_weight_composed
          left_kernel_composed])
  have root_branches_product_measurable:
      "((\<lambda>z :: slp_point \<times>
          ('i, 'j) slp_mixed_center_finite_coordinates.
        root_weight (fst (snd z)) *
          slp_left_branch_complex_kernel_joint left_cutoff left_potential
            left_terminal_value
            (fst (slp_mixed_center_finite_inserted_coordinates
              (fst z) (snd z))) *
          slp_right_branch_complex_kernel_joint right_cutoff right_potential
            right_terminal_value
            (snd (slp_mixed_center_finite_inserted_coordinates
              (fst z) (snd z))))) \<in> borel_measurable lborel"
    by (rule borel_measurable_times[OF root_left_product_measurable
          right_kernel_composed])
  show ?thesis
    unfolding slp_mixed_center_finite_weighted_complex_amplitude_def
    by (rule borel_measurable_times[OF root_branches_product_measurable
          center_factor_composed])
qed

end
