theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Positive_Mass_Tonelli
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_006.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Center_Integrand_Factorization"
begin

section \<open>Global Tonelli form of the finite mixed positive mass\<close>

theorem slp_mixed_center_finite_positive_mass_tonelli:
  assumes root_weight_measurable[measurable]:
      "root_weight \<in> borel_measurable lborel"
    and left_cutoff_measurable[measurable]:
      "left_cutoff \<in> borel_measurable lborel"
    and left_potential_measurable[measurable]:
      "left_potential \<in> borel_measurable lborel"
    and right_cutoff_measurable[measurable]:
      "right_cutoff \<in> borel_measurable lborel"
    and right_potential_measurable[measurable]:
      "right_potential \<in> borel_measurable lborel"
  shows
    "nn_integral lborel (\<lambda>center.
        slp_mixed_center_finite_positive_fiber_mass TYPE('i::finite)
          TYPE('j::finite) R root_weight left_cutoff left_potential
          right_cutoff right_potential center) =
      nn_integral lborel (\<lambda>coordinates ::
          ('i, 'j) slp_mixed_center_finite_coordinates.
        ennreal (cmod (root_weight (fst coordinates))) *
          slp_left_branch_positive_kernel_joint R left_cutoff left_potential
            (\<lambda>_. 1) (fst coordinates, fst (snd coordinates)) *
          nn_integral lborel (\<lambda>terminal.
            slp_left_branch_positive_kernel_joint R right_cutoff
              right_potential (\<lambda>_. 1)
              (fst coordinates, (snd (snd coordinates), terminal))))"
proof -
  let ?integrand =
    "\<lambda>center (coordinates ::
        ('i, 'j) slp_mixed_center_finite_coordinates).
      ennreal (cmod (root_weight (fst coordinates))) *
        slp_left_branch_positive_kernel_joint R left_cutoff left_potential
          (\<lambda>_. 1)
          (fst (slp_mixed_center_finite_inserted_coordinates
            center coordinates)) *
        slp_left_branch_positive_kernel_joint R right_cutoff right_potential
          (\<lambda>_. 1)
          (snd (slp_mixed_center_finite_inserted_coordinates
            center coordinates))"
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
  have left_coordinates_measurable[measurable]:
      "((\<lambda>z. fst (slp_mixed_center_finite_inserted_coordinates
          (fst z) (snd z))) ::
          (slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates)
            \<Rightarrow> 'i slp_left_branch_finite_coordinates)
        \<in> borel_measurable lborel"
    using measurable_compose[OF inserted_product_measurable measurable_fst]
    by (simp add: comp_def measurable_lborel1)
  have right_coordinates_measurable[measurable]:
      "((\<lambda>z. snd (slp_mixed_center_finite_inserted_coordinates
          (fst z) (snd z))) ::
          (slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates)
            \<Rightarrow> 'j slp_left_branch_finite_coordinates)
        \<in> borel_measurable lborel"
    using measurable_compose[OF inserted_product_measurable measurable_snd]
    by (simp add: comp_def measurable_lborel1)
  have left_kernel_measurable[measurable]:
      "(slp_left_branch_positive_kernel_joint R left_cutoff left_potential
          (\<lambda>_. 1) ::
        'i slp_left_branch_finite_coordinates \<Rightarrow> ennreal)
        \<in> borel_measurable lborel"
    by (rule slp_left_branch_positive_kernel_joint_measurable[OF
          left_cutoff_measurable left_potential_measurable]) measurable
  have right_kernel_measurable[measurable]:
      "(slp_left_branch_positive_kernel_joint R right_cutoff right_potential
          (\<lambda>_. 1) ::
        'j slp_left_branch_finite_coordinates \<Rightarrow> ennreal)
        \<in> borel_measurable lborel"
    by (rule slp_left_branch_positive_kernel_joint_measurable[OF
          right_cutoff_measurable right_potential_measurable]) measurable
  have left_kernel_borel_measurable:
      "(slp_left_branch_positive_kernel_joint R left_cutoff left_potential
          (\<lambda>_. 1) ::
        'i slp_left_branch_finite_coordinates \<Rightarrow> ennreal)
        \<in> borel_measurable borel"
    using left_kernel_measurable by (simp only: measurable_lborel2)
  have right_kernel_borel_measurable:
      "(slp_left_branch_positive_kernel_joint R right_cutoff right_potential
          (\<lambda>_. 1) ::
        'j slp_left_branch_finite_coordinates \<Rightarrow> ennreal)
        \<in> borel_measurable borel"
    using right_kernel_measurable by (simp only: measurable_lborel2)
  have left_kernel_composed[measurable]:
      "((\<lambda>z. slp_left_branch_positive_kernel_joint R left_cutoff
          left_potential (\<lambda>_. 1)
          (fst (slp_mixed_center_finite_inserted_coordinates
            (fst z) (snd z)))) ::
          (slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates)
            \<Rightarrow> ennreal)
        \<in> borel_measurable lborel"
    using measurable_compose[OF left_coordinates_measurable
      left_kernel_borel_measurable]
    unfolding comp_def .
  have right_kernel_composed[measurable]:
      "((\<lambda>z. slp_left_branch_positive_kernel_joint R right_cutoff
          right_potential (\<lambda>_. 1)
          (snd (slp_mixed_center_finite_inserted_coordinates
            (fst z) (snd z)))) ::
          (slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates)
            \<Rightarrow> ennreal)
        \<in> borel_measurable lborel"
    using measurable_compose[OF right_coordinates_measurable
      right_kernel_borel_measurable]
    unfolding comp_def .
  have root_coordinates_measurable[measurable]:
      "((\<lambda>z :: slp_point \<times>
          ('i, 'j) slp_mixed_center_finite_coordinates. fst (snd z)))
        \<in> borel_measurable lborel"
    apply (simp only: measurable_lborel2)
    by (rule borel_measurable_continuous_onI) (intro continuous_intros)
  have root_weight_borel_measurable:
      "root_weight \<in> borel_measurable borel"
    using root_weight_measurable by (simp only: measurable_lborel2)
  have root_weight_composed[measurable]:
      "((\<lambda>z :: slp_point \<times>
          ('i, 'j) slp_mixed_center_finite_coordinates.
        root_weight (fst (snd z)))) \<in> borel_measurable lborel"
    by (rule measurable_compose[OF root_coordinates_measurable
          root_weight_borel_measurable])
  have integrand_lborel_measurable:
      "case_prod ?integrand \<in> borel_measurable lborel"
    by measurable
  have integrand_measurable:
      "case_prod ?integrand \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    using integrand_lborel_measurable by (simp only: lborel_prod)
  have swap:
      "nn_integral lborel (\<lambda>center.
          nn_integral lborel (\<lambda>coordinates.
            ?integrand center coordinates)) =
        nn_integral lborel (\<lambda>coordinates.
          nn_integral lborel (\<lambda>center.
            ?integrand center coordinates))"
    using lborel_pair.Fubini'[OF integrand_measurable] by simp
  have integrate_center:
      "nn_integral lborel (\<lambda>center.
          ?integrand center coordinates) =
        ennreal (cmod (root_weight (fst coordinates))) *
          slp_left_branch_positive_kernel_joint R left_cutoff left_potential
            (\<lambda>_. 1) (fst coordinates, fst (snd coordinates)) *
          nn_integral lborel (\<lambda>terminal.
            slp_left_branch_positive_kernel_joint R right_cutoff
              right_potential (\<lambda>_. 1)
              (fst coordinates, (snd (snd coordinates), terminal)))"
    for coordinates :: "('i, 'j) slp_mixed_center_finite_coordinates"
    using slp_mixed_center_finite_positive_integrand_center_factorization[
      OF right_cutoff_measurable right_potential_measurable,
      where coordinates = coordinates and R = R and root_weight = root_weight
        and left_cutoff = left_cutoff and left_potential = left_potential]
    by (simp only: slp_mixed_center_finite_inserted_coordinates_def prod.sel)
  show ?thesis
    unfolding slp_mixed_center_finite_positive_fiber_mass_def
    using swap
    by (simp only: integrate_center)
qed

end
