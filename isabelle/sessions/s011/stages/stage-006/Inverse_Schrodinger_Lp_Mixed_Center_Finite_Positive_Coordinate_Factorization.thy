theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Positive_Coordinate_Factorization
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_006.Inverse_Schrodinger_Lp_One_Sided_Finite_Unit_Inner_Mass_Measurable"
begin

section \<open>Finite mixed positive coordinate-mass factorization\<close>

theorem slp_mixed_center_finite_positive_coordinate_factorization:
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
    "nn_integral lborel (\<lambda>coordinates ::
        ('i::finite, 'j::finite) slp_mixed_center_finite_coordinates.
      ennreal (cmod (root_weight (fst coordinates))) *
        slp_left_branch_positive_kernel_joint R left_cutoff left_potential
          (\<lambda>_. 1) (fst coordinates, fst (snd coordinates)) *
        nn_integral lborel (\<lambda>terminal.
          slp_left_branch_positive_kernel_joint R right_cutoff
            right_potential (\<lambda>_. 1)
            (fst coordinates, (snd (snd coordinates), terminal)))) =
      nn_integral lborel (\<lambda>root.
        ennreal (cmod (root_weight root)) *
          slp_left_branch_positive_inner_mass_finite TYPE('i) R
            left_cutoff left_potential (\<lambda>_. 1) (\<lambda>_. 1) root *
          slp_left_branch_positive_inner_mass_finite TYPE('j) R
            right_cutoff right_potential (\<lambda>_. 1) (\<lambda>_. 1) root)"
proof -
  let ?left_kernel =
    "slp_left_branch_positive_kernel_joint R left_cutoff left_potential
      (\<lambda>_. 1) :: 'i slp_left_branch_finite_coordinates \<Rightarrow> ennreal"
  let ?right_kernel =
    "slp_left_branch_positive_kernel_joint R right_cutoff right_potential
      (\<lambda>_. 1) :: 'j slp_left_branch_finite_coordinates \<Rightarrow> ennreal"
  let ?right_terminal_mass =
    "\<lambda>root branch_arrays.
      nn_integral lborel (\<lambda>terminal.
        ?right_kernel (root, (branch_arrays, terminal)))"
  let ?coordinate_integrand =
    "\<lambda>coordinates :: ('i, 'j) slp_mixed_center_finite_coordinates.
      ennreal (cmod (root_weight (fst coordinates))) *
        ?left_kernel (fst coordinates, fst (snd coordinates)) *
        ?right_terminal_mass (fst coordinates) (snd (snd coordinates))"
  have left_kernel_measurable[measurable]:
      "?left_kernel \<in> borel_measurable lborel"
    by (rule slp_left_branch_positive_kernel_joint_measurable[OF
          left_cutoff_measurable left_potential_measurable]) measurable
  have right_kernel_measurable[measurable]:
      "?right_kernel \<in> borel_measurable lborel"
    by (rule slp_left_branch_positive_kernel_joint_measurable[OF
          right_cutoff_measurable right_potential_measurable]) measurable
  have reassociate_measurable:
      "((\<lambda>z ::
          (slp_point \<times> ((slp_point^'j) \<times> (slp_point^'j)))
            \<times> slp_point.
        (fst (fst z), (snd (fst z), snd z))))
        \<in> measurable lborel lborel"
    apply (simp only: measurable_lborel1 measurable_lborel2)
    by (rule borel_measurable_continuous_onI) (intro continuous_intros)
  have right_kernel_reassociated_measurable:
      "((\<lambda>z ::
          (slp_point \<times> ((slp_point^'j) \<times> (slp_point^'j)))
            \<times> slp_point.
        ?right_kernel (fst (fst z), (snd (fst z), snd z))))
        \<in> borel_measurable lborel"
    using measurable_comp[OF reassociate_measurable right_kernel_measurable]
    by (simp only: comp_def)
  have right_kernel_reassociated_product_measurable:
      "((\<lambda>z ::
          (slp_point \<times> ((slp_point^'j) \<times> (slp_point^'j)))
            \<times> slp_point.
        ?right_kernel (fst (fst z), (snd (fst z), snd z))))
        \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    using right_kernel_reassociated_measurable
    by (simp only: lborel_prod)
  have right_terminal_mass_measurable[measurable]:
      "case_prod ?right_terminal_mass \<in> borel_measurable lborel"
    using lborel.borel_measurable_nn_integral_fst[OF
      right_kernel_reassociated_product_measurable]
    by simp
  have root_projection_measurable[measurable]:
      "((\<lambda>coordinates ::
          ('i, 'j) slp_mixed_center_finite_coordinates.
        fst coordinates)) \<in> measurable lborel lborel"
    apply (simp only: measurable_lborel1 measurable_lborel2)
    by (rule borel_measurable_continuous_onI) (intro continuous_intros)
  have left_coordinates_projection_measurable:
      "((\<lambda>coordinates ::
          ('i, 'j) slp_mixed_center_finite_coordinates.
        (fst coordinates, fst (snd coordinates))))
        \<in> measurable lborel lborel"
    apply (simp only: measurable_lborel1 measurable_lborel2)
    by (rule borel_measurable_continuous_onI) (intro continuous_intros)
  have right_arrays_projection_measurable:
      "((\<lambda>coordinates ::
          ('i, 'j) slp_mixed_center_finite_coordinates.
        (fst coordinates, snd (snd coordinates))))
        \<in> measurable lborel lborel"
    apply (simp only: measurable_lborel1 measurable_lborel2)
    by (rule borel_measurable_continuous_onI) (intro continuous_intros)
  have left_kernel_composed_measurable[measurable]:
      "((\<lambda>coordinates ::
          ('i, 'j) slp_mixed_center_finite_coordinates.
        ?left_kernel (fst coordinates, fst (snd coordinates))))
        \<in> borel_measurable lborel"
    using measurable_comp[OF left_coordinates_projection_measurable
      left_kernel_measurable]
    by (simp only: comp_def)
  have right_terminal_mass_composed_measurable[measurable]:
      "((\<lambda>coordinates ::
          ('i, 'j) slp_mixed_center_finite_coordinates.
        ?right_terminal_mass (fst coordinates) (snd (snd coordinates))))
        \<in> borel_measurable lborel"
    using measurable_comp[OF right_arrays_projection_measurable
      right_terminal_mass_measurable]
    by (simp only: comp_def case_prod_unfold prod.sel)
  have coordinate_integrand_measurable:
      "?coordinate_integrand \<in> borel_measurable lborel"
    by measurable
  have coordinate_integrand_product_measurable:
      "?coordinate_integrand \<in> borel_measurable
        (lborel \<Otimes>\<^sub>M lborel)"
    using coordinate_integrand_measurable by (simp only: lborel_prod)
  have root_split:
      "nn_integral lborel ?coordinate_integrand =
        nn_integral lborel (\<lambda>root.
          nn_integral lborel (\<lambda>branch_coordinates.
            ?coordinate_integrand (root, branch_coordinates)))"
  proof -
    note raw = lborel.nn_integral_fst[OF
      coordinate_integrand_product_measurable]
    show ?thesis
      using raw[symmetric] by (simp only: lborel_prod)
  qed
  have left_kernel_slice_measurable[measurable]:
      "(\<lambda>branch_coordinates ::
          ((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point.
        ?left_kernel (root, branch_coordinates)) \<in> borel_measurable lborel"
    for root
    by measurable
  have right_terminal_mass_slice_measurable[measurable]:
      "(\<lambda>branch_arrays :: (slp_point^'j) \<times> (slp_point^'j).
        ?right_terminal_mass root branch_arrays) \<in> borel_measurable lborel"
    for root
    by measurable
  have branch_factorization:
      "nn_integral lborel (\<lambda>branch_coordinates.
          ?coordinate_integrand (root, branch_coordinates)) =
        ennreal (cmod (root_weight root)) *
          slp_left_branch_positive_inner_mass_finite TYPE('i) R
            left_cutoff left_potential (\<lambda>_. 1) (\<lambda>_. 1) root *
          slp_left_branch_positive_inner_mass_finite TYPE('j) R
            right_cutoff right_potential (\<lambda>_. 1) (\<lambda>_. 1) root"
    for root
  proof -
    let ?branch_integrand =
      "\<lambda>z ::
          (((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point) \<times>
            ((slp_point^'j) \<times> (slp_point^'j)).
        ennreal (cmod (root_weight root)) *
          ?left_kernel (root, fst z) *
          ?right_terminal_mass root (snd z)"
    have left_branch_projection_measurable:
        "(\<lambda>z ::
            (((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point) \<times>
              ((slp_point^'j) \<times> (slp_point^'j)). fst z)
          \<in> measurable lborel lborel"
      apply (simp only: measurable_lborel1 measurable_lborel2)
      by (rule borel_measurable_continuous_onI) (intro continuous_intros)
    have right_branch_projection_measurable:
        "(\<lambda>z ::
            (((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point) \<times>
              ((slp_point^'j) \<times> (slp_point^'j)). snd z)
          \<in> measurable lborel lborel"
      apply (simp only: measurable_lborel1 measurable_lborel2)
      by (rule borel_measurable_continuous_onI) (intro continuous_intros)
    have left_slice_composed_measurable[measurable]:
        "((\<lambda>z ::
            (((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point) \<times>
              ((slp_point^'j) \<times> (slp_point^'j)).
          ?left_kernel (root, fst z))) \<in> borel_measurable lborel"
      using measurable_comp[OF left_branch_projection_measurable
        left_kernel_slice_measurable]
      by (simp only: comp_def)
    have right_slice_composed_measurable[measurable]:
        "((\<lambda>z ::
            (((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point) \<times>
              ((slp_point^'j) \<times> (slp_point^'j)).
          ?right_terminal_mass root (snd z))) \<in> borel_measurable lborel"
      using measurable_comp[OF right_branch_projection_measurable
        right_terminal_mass_slice_measurable]
      by (simp only: comp_def)
    have branch_integrand_measurable:
        "?branch_integrand \<in> borel_measurable lborel"
      by measurable
    have branch_integrand_product_measurable:
        "?branch_integrand \<in> borel_measurable
          (lborel \<Otimes>\<^sub>M lborel)"
      using branch_integrand_measurable by (simp only: lborel_prod)
    have split_branches:
        "nn_integral lborel ?branch_integrand =
          nn_integral lborel (\<lambda>left_coordinates.
            nn_integral lborel (\<lambda>right_arrays.
              ?branch_integrand (left_coordinates, right_arrays)))"
    proof -
      note raw = lborel.nn_integral_fst[OF
        branch_integrand_product_measurable]
      show ?thesis
        using raw[symmetric] by (simp only: lborel_prod)
    qed
    have right_mass:
        "nn_integral lborel (\<lambda>right_arrays.
            ?right_terminal_mass root right_arrays) =
          slp_left_branch_positive_inner_mass_finite TYPE('j) R
            right_cutoff right_potential (\<lambda>_. 1) (\<lambda>_. 1) root"
      using slp_left_branch_positive_inner_mass_finite_unit_split[
        OF right_cutoff_measurable right_potential_measurable,
        where root = root and R = R and 'i = 'j]
      by simp
    have integrate_right:
        "nn_integral lborel (\<lambda>right_arrays.
            ?branch_integrand (left_coordinates, right_arrays)) =
          ennreal (cmod (root_weight root)) *
            ?left_kernel (root, left_coordinates) *
            slp_left_branch_positive_inner_mass_finite TYPE('j) R
              right_cutoff right_potential (\<lambda>_. 1) (\<lambda>_. 1) root"
      for left_coordinates
    proof -
      have right_slice:
          "(\<lambda>right_arrays :: (slp_point^'j) \<times> (slp_point^'j).
            ?right_terminal_mass root right_arrays)
            \<in> borel_measurable lborel"
        by (rule right_terminal_mass_slice_measurable)
      note raw = nn_integral_cmult[OF right_slice,
        where c = "ennreal (cmod (root_weight root)) *
          ?left_kernel (root, left_coordinates)"]
      show ?thesis
        using raw right_mass
        by (simp only: prod.sel mult.assoc)
    qed
    have left_mass:
        "nn_integral lborel (\<lambda>left_coordinates.
            ?left_kernel (root, left_coordinates)) =
          slp_left_branch_positive_inner_mass_finite TYPE('i) R
            left_cutoff left_potential (\<lambda>_. 1) (\<lambda>_. 1) root"
      unfolding slp_left_branch_positive_inner_mass_finite_def
      by (simp only: norm_one ennreal_1 mult_1_right)
    have left_slice:
        "(\<lambda>left_coordinates ::
            ((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point.
          ?left_kernel (root, left_coordinates)) \<in> borel_measurable lborel"
      by (rule left_kernel_slice_measurable)
    have left_scaled_measurable:
        "(\<lambda>left_coordinates ::
            ((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point.
          ennreal (cmod (root_weight root)) *
            ?left_kernel (root, left_coordinates))
          \<in> borel_measurable lborel"
      by measurable
    have after_right:
        "nn_integral lborel (\<lambda>left_coordinates.
            nn_integral lborel (\<lambda>right_arrays.
              ?branch_integrand (left_coordinates, right_arrays))) =
          nn_integral lborel (\<lambda>left_coordinates.
            ennreal (cmod (root_weight root)) *
              ?left_kernel (root, left_coordinates) *
              slp_left_branch_positive_inner_mass_finite TYPE('j) R
                right_cutoff right_potential (\<lambda>_. 1) (\<lambda>_. 1) root)"
      by (rule nn_integral_cong) (simp only: integrate_right)
    have integrate_left:
        "nn_integral lborel (\<lambda>left_coordinates.
            ennreal (cmod (root_weight root)) *
              ?left_kernel (root, left_coordinates) *
              slp_left_branch_positive_inner_mass_finite TYPE('j) R
                right_cutoff right_potential (\<lambda>_. 1) (\<lambda>_. 1) root) =
          ennreal (cmod (root_weight root)) *
            slp_left_branch_positive_inner_mass_finite TYPE('i) R
              left_cutoff left_potential (\<lambda>_. 1) (\<lambda>_. 1) root *
            slp_left_branch_positive_inner_mass_finite TYPE('j) R
              right_cutoff right_potential (\<lambda>_. 1) (\<lambda>_. 1) root"
    proof -
      note pull_right = nn_integral_multc[OF left_scaled_measurable,
        where c = "slp_left_branch_positive_inner_mass_finite TYPE('j) R
          right_cutoff right_potential (\<lambda>_. 1) (\<lambda>_. 1) root"]
      note pull_root = nn_integral_cmult[OF left_slice,
        where c = "ennreal (cmod (root_weight root))"]
      show ?thesis
        using pull_right pull_root left_mass
        by (simp only: mult.assoc)
    qed
    have coordinate_as_branch:
        "nn_integral lborel (\<lambda>branch_coordinates.
            ?coordinate_integrand (root, branch_coordinates)) =
          nn_integral lborel ?branch_integrand"
      by (simp only: prod.sel)
    note first_two = trans[OF coordinate_as_branch split_branches]
    note first_three = trans[OF first_two after_right]
    show ?thesis
      using trans[OF first_three integrate_left] .
  qed
  show ?thesis
    using root_split
    by (simp only: branch_factorization)
qed

end
