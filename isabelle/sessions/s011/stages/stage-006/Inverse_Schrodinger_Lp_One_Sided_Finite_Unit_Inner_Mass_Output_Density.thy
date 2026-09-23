theory Inverse_Schrodinger_Lp_One_Sided_Finite_Unit_Inner_Mass_Output_Density
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_006.Inverse_Schrodinger_Lp_Positive_Kernel_Joint_Fixed_Output_Integral"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_006.Inverse_Schrodinger_Lp_One_Sided_Finite_Unit_Inner_Mass_Split"
begin

section \<open>Finite unit inner mass as output-density mass\<close>

theorem slp_left_branch_positive_inner_mass_finite_unit_output_density:
  fixes branch_dummy :: "'i::finite itself"
    and root :: slp_point
  assumes cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and potential_measurable[measurable]:
      "potential \<in> borel_measurable lborel"
  shows
    "slp_left_branch_positive_inner_mass_finite TYPE('i) R cutoff
        potential (\<lambda>_. 1) (\<lambda>_. 1) root =
      nn_integral lborel
        (slp_positive_output_density R cutoff potential (\<lambda>_. 1)
          CARD('i) root)"
proof -
  let ?branch_output =
    "\<lambda>branch_arrays :: (slp_point^'i) \<times> (slp_point^'i).
      slp_left_branch_output
        (slp_finite_branch_pair_list
          (\<lambda>i. fst branch_arrays $ i)
          (\<lambda>i. snd branch_arrays $ i)) 0"
  let ?kernel =
    "\<lambda>(branch_arrays :: (slp_point^'i) \<times> (slp_point^'i)) terminal.
      slp_left_branch_positive_kernel_joint R cutoff potential
        (\<lambda>_. 1) (root, (branch_arrays, terminal))"
  let ?fixed_kernel =
    "\<lambda>branch_arrays target.
      ?kernel branch_arrays (target - ?branch_output branch_arrays)"
  have arrays_to_coordinates_measurable:
      "(\<lambda>branch_arrays :: (slp_point^'i) \<times> (slp_point^'i).
        (0, (branch_arrays, 0)) :: 'i slp_left_branch_finite_coordinates)
        \<in> measurable lborel lborel"
    apply (simp only: measurable_lborel1 measurable_lborel2)
    by (rule borel_measurable_continuous_onI) (intro continuous_intros)
  have branch_output_measurable[measurable]:
      "?branch_output \<in> borel_measurable lborel"
    using measurable_comp[OF arrays_to_coordinates_measurable
      slp_left_branch_finite_output_measurable]
    by (simp only: comp_def prod.sel)
  have joint_kernel_measurable:
      "(slp_left_branch_positive_kernel_joint R cutoff potential
          (\<lambda>_. 1) ::
        'i slp_left_branch_finite_coordinates \<Rightarrow> ennreal)
        \<in> borel_measurable lborel"
    by (rule slp_left_branch_positive_kernel_joint_measurable[OF
          cutoff_measurable potential_measurable]) measurable
  have arrays_projection_measurable:
      "(\<lambda>z :: ((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point.
        fst z) \<in> measurable lborel lborel"
    apply (simp only: measurable_lborel1 measurable_lborel2)
    by (rule borel_measurable_continuous_onI) (intro continuous_intros)
  have branch_output_composed[measurable]:
      "(\<lambda>z :: ((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point.
        ?branch_output (fst z)) \<in> borel_measurable lborel"
    using measurable_comp[OF arrays_projection_measurable
      branch_output_measurable]
    by (simp only: comp_def)
  have terminal_projection_lborel:
      "(\<lambda>z :: ((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point.
        snd z) \<in> measurable lborel lborel"
    apply (simp only: measurable_lborel1 measurable_lborel2)
    by (rule borel_measurable_continuous_onI) (intro continuous_intros)
  have terminal_projection[measurable]:
      "(\<lambda>z :: ((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point.
        snd z) \<in> borel_measurable lborel"
    using terminal_projection_lborel by (simp only: measurable_lborel1)
  have adjusted_terminal_borel:
      "(\<lambda>z :: ((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point.
        snd z - ?branch_output (fst z)) \<in> borel_measurable lborel"
    by measurable
  have adjusted_terminal_measurable:
      "(\<lambda>z :: ((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point.
        snd z - ?branch_output (fst z)) \<in> measurable lborel lborel"
    using adjusted_terminal_borel by (simp only: measurable_lborel1)
  have inner_coordinates_measurable:
      "(\<lambda>z :: ((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point.
        (fst z, snd z - ?branch_output (fst z)))
        \<in> measurable lborel lborel"
  proof -
    note raw = measurable_Pair[OF arrays_projection_measurable
      adjusted_terminal_measurable]
    show ?thesis
      using raw by (simp only: lborel_prod)
  qed
  have root_measurable:
      "(\<lambda>_ :: ((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point.
        root) \<in> measurable lborel lborel"
    by measurable
  have fixed_coordinates_measurable:
      "((\<lambda>z ::
          ((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point.
        (root, (fst z, snd z - ?branch_output (fst z)))) ::
          (((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point)
            \<Rightarrow> 'i slp_left_branch_finite_coordinates)
        \<in> measurable lborel lborel"
  proof -
    note raw = measurable_Pair[OF root_measurable
      inner_coordinates_measurable]
    show ?thesis
      using raw by (simp only: lborel_prod)
  qed
  have fixed_kernel_measurable:
      "case_prod ?fixed_kernel \<in> borel_measurable lborel"
    using measurable_comp[OF fixed_coordinates_measurable
      joint_kernel_measurable]
    by (simp only: comp_def case_prod_unfold)
  have fixed_kernel_product_measurable:
      "case_prod ?fixed_kernel \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    using fixed_kernel_measurable by (simp only: lborel_prod)
  have terminal_kernel_measurable:
      "?kernel branch_arrays \<in> borel_measurable lborel"
    for branch_arrays
  proof -
    have terminal_coordinates_measurable:
        "(\<lambda>terminal.
          (root, ((branch_arrays ::
              (slp_point^'i) \<times> (slp_point^'i)), terminal)) ::
            'i slp_left_branch_finite_coordinates)
          \<in> measurable lborel lborel"
      apply (simp only: measurable_lborel1 measurable_lborel2)
      by (rule borel_measurable_continuous_onI) (intro continuous_intros)
    show ?thesis
      using measurable_comp[OF terminal_coordinates_measurable
        joint_kernel_measurable]
      by (simp only: comp_def)
  qed
  have translate_terminal:
      "nn_integral lborel (\<lambda>target.
          ?fixed_kernel branch_arrays target) =
        nn_integral lborel (?kernel branch_arrays)"
    for branch_arrays
  proof -
    note translated = slp_nn_integral_translate[
      OF terminal_kernel_measurable,
      where shift = "- ?branch_output branch_arrays"]
    show ?thesis
      using translated by (simp add: algebra_simps)
  qed
  have translate_all:
      "nn_integral lborel (\<lambda>branch_arrays.
          nn_integral lborel (?kernel branch_arrays)) =
        nn_integral lborel (\<lambda>branch_arrays.
          nn_integral lborel (\<lambda>target.
            ?fixed_kernel branch_arrays target))"
    by (rule nn_integral_cong) (simp only: translate_terminal)
  have swap:
      "nn_integral lborel (\<lambda>branch_arrays.
          nn_integral lborel (\<lambda>target.
            ?fixed_kernel branch_arrays target)) =
        nn_integral lborel (\<lambda>target.
          nn_integral lborel (\<lambda>branch_arrays.
            ?fixed_kernel branch_arrays target))"
    using lborel_pair.Fubini'[OF fixed_kernel_product_measurable] by simp
  have identify_density:
      "nn_integral lborel (\<lambda>branch_arrays.
          ?fixed_kernel branch_arrays target) =
        slp_positive_output_density R cutoff potential (\<lambda>_. 1)
          CARD('i) root target"
    for target
  proof -
    have terminal_one_measurable:
        "(\<lambda>_ :: slp_point. 1 :: complex) \<in> borel_measurable lborel"
      by measurable
    show ?thesis
      using slp_left_branch_positive_kernel_joint_fixed_output_integral[
        where R = R and cutoff = cutoff and potential = potential
          and terminal_value = "\<lambda>_. 1" and origin = root
          and target = target and 'i = 'i,
        OF cutoff_measurable potential_measurable terminal_one_measurable]
      by (simp only: norm_one ennreal_1 split_beta' prod.sel prod.collapse)
  qed
  note split = slp_left_branch_positive_inner_mass_finite_unit_split[
    OF cutoff_measurable potential_measurable,
    where root = root and R = R and 'i = 'i]
  note first = trans[OF split translate_all]
  note second = trans[OF first swap]
  show ?thesis
    using second by (simp only: identify_density)
qed

end
