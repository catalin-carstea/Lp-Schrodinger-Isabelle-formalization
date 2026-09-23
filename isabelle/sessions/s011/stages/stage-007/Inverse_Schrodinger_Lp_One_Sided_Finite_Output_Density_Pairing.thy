theory Inverse_Schrodinger_Lp_One_Sided_Finite_Output_Density_Pairing
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_006.Inverse_Schrodinger_Lp_One_Sided_Finite_Unit_Inner_Mass_Output_Density"
begin

section \<open>Finite positive kernels paired through their output density\<close>

theorem slp_left_branch_positive_kernel_joint_output_density_pairing:
  fixes branch_dummy :: "'i::finite itself"
    and root :: slp_point
  assumes cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and potential_measurable[measurable]:
      "potential \<in> borel_measurable lborel"
    and terminal_value_measurable[measurable]:
      "terminal_value \<in> borel_measurable lborel"
    and output_test_measurable[measurable]:
      "output_test \<in> borel_measurable lborel"
  shows
    "(\<integral>\<^sup>+ (branch_arrays ::
          (slp_point^'i) \<times> (slp_point^'i)).
        \<integral>\<^sup>+ terminal.
          slp_left_branch_positive_kernel_joint R cutoff potential
              terminal_value (root, (branch_arrays, terminal)) *
            output_test
              (slp_left_branch_output
                (slp_finite_branch_pair_list
                  (\<lambda>i. fst branch_arrays $ i)
                  (\<lambda>i. snd branch_arrays $ i)) terminal)
          \<partial>lborel \<partial>lborel) =
      (\<integral>\<^sup>+ target.
        output_test target *
          slp_positive_output_density R cutoff potential
            (\<lambda>x. ennreal (norm (terminal_value x)))
            CARD('i) root target
        \<partial>lborel)"
proof -
  let ?pairs =
    "\<lambda>branch_arrays :: (slp_point^'i) \<times> (slp_point^'i).
      slp_finite_branch_pair_list
        (\<lambda>i. fst branch_arrays $ i)
        (\<lambda>i. snd branch_arrays $ i)"
  let ?branch_output =
    "\<lambda>branch_arrays :: (slp_point^'i) \<times> (slp_point^'i).
      slp_left_branch_output (?pairs branch_arrays) 0"
  let ?kernel =
    "\<lambda>(branch_arrays :: (slp_point^'i) \<times> (slp_point^'i)) terminal.
      slp_left_branch_positive_kernel_joint R cutoff potential
        terminal_value (root, (branch_arrays, terminal))"
  let ?weighted_kernel =
    "\<lambda>branch_arrays terminal.
      ?kernel branch_arrays terminal *
        output_test
          (slp_left_branch_output (?pairs branch_arrays) terminal)"
  let ?fixed_kernel =
    "\<lambda>branch_arrays target.
      ?kernel branch_arrays (target - ?branch_output branch_arrays)"
  let ?fixed_weighted =
    "\<lambda>branch_arrays target.
      ?fixed_kernel branch_arrays target * output_test target"
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
          terminal_value ::
        'i slp_left_branch_finite_coordinates \<Rightarrow> ennreal)
        \<in> borel_measurable lborel"
    by (rule slp_left_branch_positive_kernel_joint_measurable[OF
          cutoff_measurable potential_measurable
          terminal_value_measurable])
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
  have output_test_target_measurable:
      "(\<lambda>z :: ((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point.
        output_test (snd z)) \<in> borel_measurable lborel"
    using measurable_comp[OF terminal_projection_lborel
      output_test_measurable]
    by (simp only: comp_def)
  have fixed_kernel_borel_measurable[measurable]:
      "case_prod ?fixed_kernel \<in> borel_measurable borel"
    using fixed_kernel_measurable by (simp only: measurable_lborel2)
  have output_test_target_borel_measurable[measurable]:
      "(\<lambda>z :: ((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point.
        output_test (snd z)) \<in> borel_measurable borel"
    using output_test_target_measurable by (simp only: measurable_lborel2)
  have fixed_weighted_borel_measurable:
      "case_prod ?fixed_weighted \<in> borel_measurable borel"
    using borel_measurable_times_ennreal[
      OF fixed_kernel_borel_measurable
        output_test_target_borel_measurable]
    by (simp only: case_prod_unfold)
  have fixed_weighted_measurable:
      "case_prod ?fixed_weighted \<in> borel_measurable lborel"
    using fixed_weighted_borel_measurable
    by (simp only: measurable_lborel2)
  have fixed_weighted_product_measurable:
      "case_prod ?fixed_weighted \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    using fixed_weighted_measurable by (simp only: lborel_prod)
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
  have terminal_output_measurable:
      "(\<lambda>terminal.
        slp_left_branch_output (?pairs branch_arrays) terminal)
        \<in> borel_measurable lborel"
    for branch_arrays
    unfolding slp_left_branch_output_def
    by measurable
  have weighted_terminal_measurable:
      "?weighted_kernel branch_arrays \<in> borel_measurable lborel"
    for branch_arrays
    using terminal_kernel_measurable[of branch_arrays]
      terminal_output_measurable[of branch_arrays]
    by measurable
  have translate_terminal:
      "nn_integral lborel (\<lambda>target.
          ?fixed_weighted branch_arrays target) =
        nn_integral lborel (?weighted_kernel branch_arrays)"
    for branch_arrays
  proof -
    note translated = slp_nn_integral_translate[
      OF weighted_terminal_measurable[of branch_arrays],
      where shift = "- ?branch_output branch_arrays"]
    show ?thesis
      using translated
      by (simp add: slp_left_branch_output_def algebra_simps)
  qed
  have translate_all:
      "nn_integral lborel (\<lambda>branch_arrays.
          nn_integral lborel (?weighted_kernel branch_arrays)) =
        nn_integral lborel (\<lambda>branch_arrays.
          nn_integral lborel (\<lambda>target.
            ?fixed_weighted branch_arrays target))"
    by (rule nn_integral_cong) (simp only: translate_terminal)
  have swap:
      "nn_integral lborel (\<lambda>branch_arrays.
          nn_integral lborel (\<lambda>target.
            ?fixed_weighted branch_arrays target)) =
        nn_integral lborel (\<lambda>target.
          nn_integral lborel (\<lambda>branch_arrays.
            ?fixed_weighted branch_arrays target))"
    using lborel_pair.Fubini'[OF fixed_weighted_product_measurable] by simp
  have fixed_kernel_slice_measurable:
      "(\<lambda>branch_arrays.
        ?fixed_kernel branch_arrays target) \<in> borel_measurable lborel"
    for target
  proof -
    have insert_target_measurable:
        "(\<lambda>branch_arrays :: (slp_point^'i) \<times> (slp_point^'i).
          (branch_arrays, target)) \<in> measurable lborel lborel"
      apply (simp only: measurable_lborel1 measurable_lborel2)
      by (rule borel_measurable_continuous_onI) (intro continuous_intros)
    show ?thesis
      using measurable_comp[OF insert_target_measurable
        fixed_kernel_measurable]
      by (simp only: comp_def case_prod_unfold prod.sel)
  qed
  have pull_test:
      "nn_integral lborel (\<lambda>branch_arrays.
          ?fixed_weighted branch_arrays target) =
        output_test target *
          nn_integral lborel (\<lambda>branch_arrays.
            ?fixed_kernel branch_arrays target)"
    for target
  proof -
    note pulled = nn_integral_cmult[
      OF fixed_kernel_slice_measurable[of target],
      where c = "output_test target"]
    show ?thesis
      using pulled by (simp add: mult.commute)
  qed
  have identify_density:
      "nn_integral lborel (\<lambda>branch_arrays.
          ?fixed_kernel branch_arrays target) =
        slp_positive_output_density R cutoff potential
          (\<lambda>x. ennreal (norm (terminal_value x)))
          CARD('i) root target"
    for target
    using slp_left_branch_positive_kernel_joint_fixed_output_integral[
      where R = R and cutoff = cutoff and potential = potential
        and terminal_value = terminal_value and origin = root
        and target = target and 'i = 'i,
      OF cutoff_measurable potential_measurable terminal_value_measurable]
    by (simp only: split_beta' prod.sel prod.collapse)
  have collapse_target:
      "nn_integral lborel (\<lambda>branch_arrays.
          ?fixed_weighted branch_arrays target) =
        output_test target *
          slp_positive_output_density R cutoff potential
            (\<lambda>x. ennreal (norm (terminal_value x)))
            CARD('i) root target"
    for target
    using pull_test[of target] identify_density[of target]
    by simp
  note first = trans[OF translate_all swap]
  show ?thesis
    using first by (simp only: collapse_target)
qed

end
