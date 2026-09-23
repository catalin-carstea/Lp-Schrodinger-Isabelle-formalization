theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Positive_Fiber_Mass_Measurable
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_007.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Positive_Fiber_Mass"
begin

section \<open>Measurability of the weighted finite positive fiber mass\<close>

theorem slp_mixed_center_finite_weighted_positive_fiber_mass_measurable:
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
    "(\<lambda>center.
        slp_mixed_center_finite_weighted_positive_fiber_mass
          TYPE('i::finite) TYPE('j::finite) R root_weight left_cutoff
          left_potential left_terminal_value right_cutoff right_potential
          right_terminal_value center_factor center)
      \<in> borel_measurable lborel"
proof -
  let ?integrand =
    "\<lambda>center (coordinates ::
        ('i, 'j) slp_mixed_center_finite_coordinates).
      ennreal (cmod (root_weight (fst coordinates))) *
        slp_left_branch_positive_kernel_joint R left_cutoff left_potential
          left_terminal_value
          (fst (slp_mixed_center_finite_inserted_coordinates
            center coordinates)) *
        slp_left_branch_positive_kernel_joint R right_cutoff right_potential
          right_terminal_value
          (snd (slp_mixed_center_finite_inserted_coordinates
            center coordinates)) *
        ennreal (cmod (center_factor center))"
  have inserted_measurable:
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
    using inserted_measurable
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
  have left_kernel_measurable:
      "(slp_left_branch_positive_kernel_joint R left_cutoff left_potential
          left_terminal_value ::
        'i slp_left_branch_finite_coordinates \<Rightarrow> ennreal)
        \<in> borel_measurable lborel"
    by (rule slp_left_branch_positive_kernel_joint_measurable[OF
          left_cutoff_measurable left_potential_measurable
          left_terminal_measurable])
  have right_kernel_measurable:
      "(slp_left_branch_positive_kernel_joint R right_cutoff right_potential
          right_terminal_value ::
        'j slp_left_branch_finite_coordinates \<Rightarrow> ennreal)
        \<in> borel_measurable lborel"
    by (rule slp_left_branch_positive_kernel_joint_measurable[OF
          right_cutoff_measurable right_potential_measurable
          right_terminal_measurable])
  have left_kernel_borel_measurable:
      "(slp_left_branch_positive_kernel_joint R left_cutoff left_potential
          left_terminal_value ::
        'i slp_left_branch_finite_coordinates \<Rightarrow> ennreal)
        \<in> borel_measurable borel"
    using left_kernel_measurable by (simp only: measurable_lborel2)
  have right_kernel_borel_measurable:
      "(slp_left_branch_positive_kernel_joint R right_cutoff right_potential
          right_terminal_value ::
        'j slp_left_branch_finite_coordinates \<Rightarrow> ennreal)
        \<in> borel_measurable borel"
    using right_kernel_measurable by (simp only: measurable_lborel2)
  have left_kernel_composed[measurable]:
      "((\<lambda>z. slp_left_branch_positive_kernel_joint R left_cutoff
          left_potential left_terminal_value
          (fst (slp_mixed_center_finite_inserted_coordinates
            (fst z) (snd z)))) ::
        (slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates) \<Rightarrow>
          ennreal) \<in> borel_measurable lborel"
    using measurable_compose[OF left_coordinates_measurable
      left_kernel_borel_measurable]
    unfolding comp_def .
  have right_kernel_composed[measurable]:
      "((\<lambda>z. slp_left_branch_positive_kernel_joint R right_cutoff
          right_potential right_terminal_value
          (snd (slp_mixed_center_finite_inserted_coordinates
            (fst z) (snd z)))) ::
        (slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates) \<Rightarrow>
          ennreal) \<in> borel_measurable lborel"
    using measurable_compose[OF right_coordinates_measurable
      right_kernel_borel_measurable]
    unfolding comp_def .
  have root_coordinates_measurable[measurable]:
      "((\<lambda>z :: slp_point \<times>
          ('i, 'j) slp_mixed_center_finite_coordinates. fst (snd z)))
        \<in> borel_measurable lborel"
    apply (simp only: measurable_lborel2)
    by (rule borel_measurable_continuous_onI) (intro continuous_intros)
  have center_coordinates_measurable[measurable]:
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
  have root_norm_composed:
      "((\<lambda>z :: slp_point \<times>
          ('i, 'j) slp_mixed_center_finite_coordinates.
        ennreal (cmod (root_weight (fst (snd z))))))
        \<in> borel_measurable lborel"
    using root_weight_composed by measurable
  have center_norm_composed:
      "((\<lambda>z :: slp_point \<times>
          ('i, 'j) slp_mixed_center_finite_coordinates.
        ennreal (cmod (center_factor (fst z)))))
        \<in> borel_measurable lborel"
    using center_factor_composed by measurable
  have root_left_product_measurable:
      "((\<lambda>z :: slp_point \<times>
          ('i, 'j) slp_mixed_center_finite_coordinates.
        ennreal (cmod (root_weight (fst (snd z)))) *
          slp_left_branch_positive_kernel_joint R left_cutoff left_potential
            left_terminal_value
            (fst (slp_mixed_center_finite_inserted_coordinates
              (fst z) (snd z))))) \<in> borel_measurable lborel"
    using root_norm_composed left_kernel_composed by measurable
  have root_branches_product_measurable:
      "((\<lambda>z :: slp_point \<times>
          ('i, 'j) slp_mixed_center_finite_coordinates.
        ennreal (cmod (root_weight (fst (snd z)))) *
          slp_left_branch_positive_kernel_joint R left_cutoff left_potential
            left_terminal_value
            (fst (slp_mixed_center_finite_inserted_coordinates
              (fst z) (snd z))) *
          slp_left_branch_positive_kernel_joint R right_cutoff right_potential
            right_terminal_value
            (snd (slp_mixed_center_finite_inserted_coordinates
              (fst z) (snd z))))) \<in> borel_measurable lborel"
    using root_left_product_measurable right_kernel_composed by measurable
  have full_product_measurable:
      "((\<lambda>z :: slp_point \<times>
          ('i, 'j) slp_mixed_center_finite_coordinates.
        ennreal (cmod (root_weight (fst (snd z)))) *
          slp_left_branch_positive_kernel_joint R left_cutoff left_potential
            left_terminal_value
            (fst (slp_mixed_center_finite_inserted_coordinates
              (fst z) (snd z))) *
          slp_left_branch_positive_kernel_joint R right_cutoff right_potential
            right_terminal_value
            (snd (slp_mixed_center_finite_inserted_coordinates
              (fst z) (snd z))) *
          ennreal (cmod (center_factor (fst z)))))
        \<in> borel_measurable lborel"
    using root_branches_product_measurable center_norm_composed by measurable
  have integrand_lborel_measurable:
      "case_prod ?integrand \<in> borel_measurable lborel"
    using full_product_measurable
    by (simp only: split_beta' fst_conv snd_conv)
  have integrand_measurable:
      "case_prod ?integrand \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    using integrand_lborel_measurable by (simp only: lborel_prod)
  have parameter_measurable:
      "(\<lambda>center. nn_integral lborel (?integrand center))
        \<in> borel_measurable lborel"
    by (rule lborel.borel_measurable_nn_integral[OF integrand_measurable])
  show ?thesis
    using parameter_measurable
    unfolding
      slp_mixed_center_finite_weighted_positive_fiber_mass_def .
qed

end
