theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Positive_Fiber_Mass_Density
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_007.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Branch_Density_Pairing"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_007.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Positive_Fiber_Mass_Measurable"
begin

section \<open>Weighted finite positive fiber mass as mixed-center density\<close>

theorem slp_mixed_center_finite_weighted_positive_fiber_mass_density:
  fixes left_dummy :: "'i::finite itself"
    and right_dummy :: "'j::finite itself"
    and R :: real
    and root_weight cutoff left_potential left_terminal_value
      right_potential right_terminal_value center_factor ::
        "slp_point \<Rightarrow> complex"
    and center :: slp_point
  assumes root_weight_measurable[measurable]:
      "root_weight \<in> borel_measurable lborel"
    and cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and left_potential_measurable[measurable]:
      "left_potential \<in> borel_measurable lborel"
    and left_terminal_measurable[measurable]:
      "left_terminal_value \<in> borel_measurable lborel"
    and right_potential_measurable[measurable]:
      "right_potential \<in> borel_measurable lborel"
    and right_terminal_measurable[measurable]:
      "right_terminal_value \<in> borel_measurable lborel"
  shows
    "slp_mixed_center_finite_weighted_positive_fiber_mass
        TYPE('i) TYPE('j) R root_weight cutoff left_potential
        left_terminal_value cutoff right_potential right_terminal_value
        center_factor center =
      ennreal (cmod (center_factor center)) *
        slp_mixed_center_density R cutoff left_potential right_potential
          (\<lambda>x. ennreal (cmod (left_terminal_value x)))
          (\<lambda>x. ennreal (cmod (right_terminal_value x)))
          CARD('i) CARD('j) root_weight center"
proof -
  let ?left_weight =
    "\<lambda>x. ennreal (cmod (left_terminal_value x))"
  let ?right_weight =
    "\<lambda>x. ennreal (cmod (right_terminal_value x))"
  let ?left_density =
    "slp_left_positive_output_density R cutoff left_potential
      ?left_weight CARD('i)"
  let ?right_density =
    "slp_right_positive_output_density R cutoff right_potential
      ?right_weight CARD('j)"
  let ?branch_kernel =
    "\<lambda>root branch_coordinates ::
        (((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point) \<times>
          ((slp_point^'j) \<times> (slp_point^'j)).
      slp_left_branch_positive_kernel_joint R cutoff left_potential
          left_terminal_value
          (fst (slp_mixed_center_finite_inserted_coordinates
            center (root, branch_coordinates))) *
        slp_left_branch_positive_kernel_joint R cutoff right_potential
          right_terminal_value
          (snd (slp_mixed_center_finite_inserted_coordinates
            center (root, branch_coordinates)))"
  let ?integrand =
    "\<lambda>coordinates :: ('i, 'j) slp_mixed_center_finite_coordinates.
      ennreal (cmod (root_weight (fst coordinates))) *
        ?branch_kernel (fst coordinates) (snd coordinates) *
        ennreal (cmod (center_factor center))"
  let ?density_inner =
    "\<lambda>root.
      nn_integral lborel (\<lambda>left_output.
        ?left_density root left_output *
          ?right_density root (center + root - left_output))"
  let ?root_inner =
    "\<lambda>root.
      nn_integral lborel (\<lambda>left_output.
        ennreal (cmod (root_weight root)) *
          ?left_density root left_output *
          ?right_density root (center + root - left_output))"
  have left_weight_measurable[measurable]:
      "?left_weight \<in> borel_measurable lborel"
    by measurable
  have right_weight_measurable[measurable]:
      "?right_weight \<in> borel_measurable lborel"
    by measurable
  have inserted_joint_measurable:
      "((\<lambda>z :: slp_point \<times>
          ('i, 'j) slp_mixed_center_finite_coordinates.
        slp_mixed_center_finite_inserted_coordinates (fst z) (snd z)))
        \<in> borel_measurable lborel"
    by (rule slp_mixed_center_finite_inserted_coordinates_measurable)
  have fix_center_measurable:
      "(\<lambda>coordinates :: ('i, 'j) slp_mixed_center_finite_coordinates.
        (center, coordinates)) \<in> measurable lborel lborel"
    apply (simp only: measurable_lborel1 measurable_lborel2)
    by (rule borel_measurable_continuous_onI) (intro continuous_intros)
  have inserted_fixed_measurable:
      "(\<lambda>coordinates :: ('i, 'j) slp_mixed_center_finite_coordinates.
        slp_mixed_center_finite_inserted_coordinates center coordinates)
        \<in> borel_measurable lborel"
    using measurable_comp[OF fix_center_measurable inserted_joint_measurable]
    by (simp only: comp_def prod.sel)
  have inserted_fixed_product_measurable:
      "(\<lambda>coordinates :: ('i, 'j) slp_mixed_center_finite_coordinates.
        slp_mixed_center_finite_inserted_coordinates center coordinates)
        \<in> measurable lborel (lborel \<Otimes>\<^sub>M lborel)"
    using inserted_fixed_measurable
    by (simp only: lborel_prod measurable_lborel1)
  have left_coordinates_measurable:
      "((\<lambda>coordinates.
        fst (slp_mixed_center_finite_inserted_coordinates
          center coordinates)) ::
        ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow>
          'i slp_left_branch_finite_coordinates)
        \<in> borel_measurable lborel"
    using measurable_compose[OF inserted_fixed_product_measurable
      measurable_fst]
    by (simp add: comp_def measurable_lborel1)
  have right_coordinates_measurable:
      "((\<lambda>coordinates.
        snd (slp_mixed_center_finite_inserted_coordinates
          center coordinates)) ::
        ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow>
          'j slp_left_branch_finite_coordinates)
        \<in> borel_measurable lborel"
    using measurable_compose[OF inserted_fixed_product_measurable
      measurable_snd]
    by (simp add: comp_def measurable_lborel1)
  have left_kernel_measurable:
      "(slp_left_branch_positive_kernel_joint R cutoff left_potential
          left_terminal_value ::
        'i slp_left_branch_finite_coordinates \<Rightarrow> ennreal)
        \<in> borel_measurable lborel"
    by (rule slp_left_branch_positive_kernel_joint_measurable[OF
          cutoff_measurable left_potential_measurable
          left_terminal_measurable])
  have right_kernel_measurable:
      "(slp_left_branch_positive_kernel_joint R cutoff right_potential
          right_terminal_value ::
        'j slp_left_branch_finite_coordinates \<Rightarrow> ennreal)
        \<in> borel_measurable lborel"
    by (rule slp_left_branch_positive_kernel_joint_measurable[OF
          cutoff_measurable right_potential_measurable
          right_terminal_measurable])
  have left_kernel_borel_measurable:
      "(slp_left_branch_positive_kernel_joint R cutoff left_potential
          left_terminal_value ::
        'i slp_left_branch_finite_coordinates \<Rightarrow> ennreal)
        \<in> borel_measurable borel"
    using left_kernel_measurable by (simp only: measurable_lborel2)
  have right_kernel_borel_measurable:
      "(slp_left_branch_positive_kernel_joint R cutoff right_potential
          right_terminal_value ::
        'j slp_left_branch_finite_coordinates \<Rightarrow> ennreal)
        \<in> borel_measurable borel"
    using right_kernel_measurable by (simp only: measurable_lborel2)
  have left_kernel_composed[measurable]:
      "((\<lambda>coordinates.
        slp_left_branch_positive_kernel_joint R cutoff left_potential
          left_terminal_value
          (fst (slp_mixed_center_finite_inserted_coordinates
            center coordinates))) ::
        ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> ennreal)
        \<in> borel_measurable lborel"
    using measurable_compose[OF left_coordinates_measurable
      left_kernel_borel_measurable]
    unfolding comp_def .
  have right_kernel_composed[measurable]:
      "((\<lambda>coordinates.
        slp_left_branch_positive_kernel_joint R cutoff right_potential
          right_terminal_value
          (snd (slp_mixed_center_finite_inserted_coordinates
            center coordinates))) ::
        ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> ennreal)
        \<in> borel_measurable lborel"
    using measurable_compose[OF right_coordinates_measurable
      right_kernel_borel_measurable]
    unfolding comp_def .
  have branch_kernel_measurable:
      "(\<lambda>coordinates ::
          ('i, 'j) slp_mixed_center_finite_coordinates.
        ?branch_kernel (fst coordinates) (snd coordinates))
        \<in> borel_measurable lborel"
  proof -
    have raw:
        "(\<lambda>coordinates ::
            ('i, 'j) slp_mixed_center_finite_coordinates.
          slp_left_branch_positive_kernel_joint R cutoff left_potential
              left_terminal_value
              (fst (slp_mixed_center_finite_inserted_coordinates
                center coordinates)) *
            slp_left_branch_positive_kernel_joint R cutoff right_potential
              right_terminal_value
              (snd (slp_mixed_center_finite_inserted_coordinates
                center coordinates)))
          \<in> borel_measurable lborel"
      by (rule borel_measurable_times_ennreal[OF
            left_kernel_composed right_kernel_composed])
    show ?thesis
      using raw by (simp only: prod.collapse)
  qed
  have root_projection_measurable[measurable]:
      "(\<lambda>coordinates ::
          ('i, 'j) slp_mixed_center_finite_coordinates.
        fst coordinates) \<in> borel_measurable lborel"
    apply (simp only: measurable_lborel2)
    by (rule borel_measurable_continuous_onI) (intro continuous_intros)
  have root_weight_borel_measurable:
      "root_weight \<in> borel_measurable borel"
    using root_weight_measurable by (simp only: measurable_lborel2)
  have root_weight_composed:
      "(\<lambda>coordinates ::
          ('i, 'j) slp_mixed_center_finite_coordinates.
        root_weight (fst coordinates)) \<in> borel_measurable lborel"
    by (rule measurable_compose[OF root_projection_measurable
          root_weight_borel_measurable])
  have root_norm_measurable:
      "(\<lambda>coordinates ::
          ('i, 'j) slp_mixed_center_finite_coordinates.
        ennreal (cmod (root_weight (fst coordinates))))
        \<in> borel_measurable lborel"
    using root_weight_composed by measurable
  have root_branch_measurable:
      "(\<lambda>coordinates ::
          ('i, 'j) slp_mixed_center_finite_coordinates.
        ennreal (cmod (root_weight (fst coordinates))) *
          ?branch_kernel (fst coordinates) (snd coordinates))
        \<in> borel_measurable lborel"
    by (rule borel_measurable_times_ennreal[OF
          root_norm_measurable branch_kernel_measurable])
  have center_norm_constant_measurable:
      "(\<lambda>_ :: ('i, 'j) slp_mixed_center_finite_coordinates.
        ennreal (cmod (center_factor center)))
        \<in> borel_measurable lborel"
    by measurable
  have integrand_measurable:
      "?integrand \<in> borel_measurable lborel"
    by (rule borel_measurable_times_ennreal[OF
          root_branch_measurable center_norm_constant_measurable])
  have integrand_product_measurable:
      "?integrand \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    using integrand_measurable by (simp only: lborel_prod)
  have mass_as_integral:
      "slp_mixed_center_finite_weighted_positive_fiber_mass
          TYPE('i) TYPE('j) R root_weight cutoff left_potential
          left_terminal_value cutoff right_potential right_terminal_value
          center_factor center =
        nn_integral lborel ?integrand"
    unfolding slp_mixed_center_finite_weighted_positive_fiber_mass_def
    by (rule nn_integral_cong) (simp add: mult.assoc)
  have root_split:
      "nn_integral lborel ?integrand =
        nn_integral lborel (\<lambda>root.
          nn_integral lborel (\<lambda>branch_coordinates.
            ?integrand (root, branch_coordinates)))"
  proof -
    note raw = lborel.nn_integral_fst[OF integrand_product_measurable]
    show ?thesis
      using raw[symmetric] by (simp only: lborel_prod)
  qed
  have branch_kernel_slice_measurable:
      "?branch_kernel root \<in> borel_measurable lborel"
    for root
  proof -
    have insert_root_measurable:
        "(\<lambda>branch_coordinates ::
            (((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point) \<times>
              ((slp_point^'j) \<times> (slp_point^'j)).
          (root, branch_coordinates)) \<in> measurable lborel lborel"
      apply (simp only: measurable_lborel1 measurable_lborel2)
      by (rule borel_measurable_continuous_onI) (intro continuous_intros)
    show ?thesis
      using measurable_comp[OF insert_root_measurable
        branch_kernel_measurable]
      by (simp only: comp_def prod.sel)
  qed
  have branch_kernel_slice_product_measurable:
      "?branch_kernel root \<in> borel_measurable
        (lborel \<Otimes>\<^sub>M lborel)"
    for root
    using branch_kernel_slice_measurable[of root]
    by (simp only: lborel_prod)
  have branch_split:
      "nn_integral lborel (?branch_kernel root) =
        nn_integral lborel (\<lambda>left_coordinates.
          nn_integral lborel (\<lambda>right_arrays.
            ?branch_kernel root (left_coordinates, right_arrays)))"
    for root
  proof -
    note raw = lborel.nn_integral_fst[OF
      branch_kernel_slice_product_measurable[of root]]
    show ?thesis
      using raw[symmetric] by (simp only: lborel_prod)
  qed
  have left_parameter_measurable:
      "(\<lambda>left_coordinates.
        nn_integral lborel (\<lambda>right_arrays.
          ?branch_kernel root (left_coordinates, right_arrays)))
        \<in> borel_measurable lborel"
    for root
    using lborel.borel_measurable_nn_integral_fst[
      OF branch_kernel_slice_product_measurable[of root]]
    by simp
  have left_parameter_product_measurable:
      "(\<lambda>left_coordinates.
        nn_integral lborel (\<lambda>right_arrays.
          ?branch_kernel root (left_coordinates, right_arrays)))
        \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    for root
    using left_parameter_measurable[of root]
    by (simp only: lborel_prod)
  have left_split:
      "nn_integral lborel (\<lambda>left_coordinates.
          nn_integral lborel (\<lambda>right_arrays.
            ?branch_kernel root (left_coordinates, right_arrays))) =
        nn_integral lborel (\<lambda>left_arrays.
          nn_integral lborel (\<lambda>left_terminal.
            nn_integral lborel (\<lambda>right_arrays.
              ?branch_kernel root
                ((left_arrays, left_terminal), right_arrays))))"
    for root
  proof -
    note raw = lborel.nn_integral_fst[OF
      left_parameter_product_measurable[of root]]
    show ?thesis
      using raw[symmetric] by (simp only: lborel_prod)
  qed
  have branch_as_nested:
      "nn_integral lborel (?branch_kernel root) =
        (\<integral>\<^sup>+ (left_arrays ::
            (slp_point^'i) \<times> (slp_point^'i)).
          \<integral>\<^sup>+ left_terminal.
            \<integral>\<^sup>+ (right_arrays ::
                (slp_point^'j) \<times> (slp_point^'j)).
              slp_left_branch_positive_kernel_joint R cutoff left_potential
                  left_terminal_value (root, (left_arrays, left_terminal)) *
                slp_left_branch_positive_kernel_joint R cutoff
                  right_potential right_terminal_value
                  (root, (right_arrays,
                    center + root -
                      slp_left_branch_output
                        (slp_finite_branch_pair_list
                          (\<lambda>i. fst left_arrays $ i)
                          (\<lambda>i. snd left_arrays $ i)) left_terminal -
                      slp_right_branch_output
                        (slp_finite_branch_pair_list
                          (\<lambda>i. fst right_arrays $ i)
                          (\<lambda>i. snd right_arrays $ i)) 0))
              \<partial>lborel \<partial>lborel \<partial>lborel)"
    for root
  proof -
    note first = trans[OF branch_split[of root] left_split[of root]]
    show ?thesis
      using first
      unfolding slp_mixed_center_finite_inserted_coordinates_def
        slp_mixed_center_finite_right_terminal_def
      by (simp only: prod.sel)
  qed
  have branch_pairing:
      "nn_integral lborel (?branch_kernel root) = ?density_inner root"
    for root
  proof -
    note pairing =
      slp_mixed_center_finite_weighted_branch_density_pairing[
        where R = R and left_cutoff = cutoff and left_potential = left_potential
          and left_terminal_value = left_terminal_value and right_cutoff = cutoff
          and right_potential = right_potential
          and right_terminal_value = right_terminal_value and root = root
          and center = center and 'i = 'i and 'j = 'j,
        OF cutoff_measurable left_potential_measurable
          left_terminal_measurable cutoff_measurable
          right_potential_measurable right_terminal_measurable]
    show ?thesis
      using trans[OF branch_as_nested[of root] pairing] .
  qed
  have left_density_joint[measurable]:
      "case_prod ?left_density \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by (rule slp_left_positive_output_density_joint_measurable[OF
          cutoff_measurable left_potential_measurable
          left_weight_measurable])
  have right_density_joint[measurable]:
      "case_prod ?right_density \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by (rule slp_right_positive_output_density_joint_measurable[OF
          cutoff_measurable right_potential_measurable
          right_weight_measurable])
  have density_pair_slice_measurable:
      "(\<lambda>left_output.
        ?left_density root left_output *
          ?right_density root (center + root - left_output))
        \<in> borel_measurable lborel"
    for root
    by measurable
  have root_density_collapse:
      "?root_inner root =
        ennreal (cmod (root_weight root)) * ?density_inner root"
    for root
  proof -
    note pulled = nn_integral_cmult[
      OF density_pair_slice_measurable[of root],
      where c = "ennreal (cmod (root_weight root))"]
    show ?thesis
      using pulled by (simp only: mult.assoc)
  qed
  have root_inner_measurable:
      "?root_inner \<in> borel_measurable lborel"
    by measurable
  have root_branch_slice_measurable:
      "(\<lambda>branch_coordinates.
        ennreal (cmod (root_weight root)) *
          ?branch_kernel root branch_coordinates)
        \<in> borel_measurable lborel"
    for root
    using branch_kernel_slice_measurable[of root]
    by measurable
  have integrate_branch:
      "nn_integral lborel (\<lambda>branch_coordinates.
          ?integrand (root, branch_coordinates)) =
        ?root_inner root * ennreal (cmod (center_factor center))"
    for root
  proof -
    note pull_center = nn_integral_multc[
      OF root_branch_slice_measurable[of root],
      where c = "ennreal (cmod (center_factor center))"]
    note pull_root = nn_integral_cmult[
      OF branch_kernel_slice_measurable[of root],
      where c = "ennreal (cmod (root_weight root))"]
    show ?thesis
      using pull_center pull_root branch_pairing[of root]
        root_density_collapse[of root]
      by (simp only: prod.sel mult.assoc)
  qed
  have after_root:
      "nn_integral lborel ?integrand =
        nn_integral lborel (\<lambda>root.
          ?root_inner root * ennreal (cmod (center_factor center)))"
    using root_split
    by (simp only: integrate_branch)
  have pull_center:
      "nn_integral lborel (\<lambda>root.
          ?root_inner root * ennreal (cmod (center_factor center))) =
        nn_integral lborel ?root_inner *
          ennreal (cmod (center_factor center))"
    by (rule nn_integral_multc[OF root_inner_measurable])
  have density_identification:
      "nn_integral lborel ?root_inner =
        slp_mixed_center_density R cutoff left_potential right_potential
          ?left_weight ?right_weight CARD('i) CARD('j) root_weight center"
    unfolding slp_mixed_center_density_def
    by simp
  show ?thesis
    using mass_as_integral after_root pull_center density_identification
    by (simp add: mult.commute)
qed

end
