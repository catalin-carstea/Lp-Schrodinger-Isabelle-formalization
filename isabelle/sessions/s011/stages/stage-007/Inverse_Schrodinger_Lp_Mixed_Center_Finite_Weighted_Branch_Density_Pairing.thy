theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Branch_Density_Pairing
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_007.Inverse_Schrodinger_Lp_One_Sided_Finite_Output_Density_Pairing"
begin

section \<open>Fixed-root weighted mixed branches through output densities\<close>

theorem slp_mixed_center_finite_weighted_branch_density_pairing:
  fixes left_dummy :: "'i::finite itself"
    and right_dummy :: "'j::finite itself"
    and root center :: slp_point
  assumes left_cutoff_measurable[measurable]:
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
  shows
    "(\<integral>\<^sup>+ (left_arrays ::
          (slp_point^'i) \<times> (slp_point^'i)).
        \<integral>\<^sup>+ left_terminal.
          \<integral>\<^sup>+ (right_arrays ::
              (slp_point^'j) \<times> (slp_point^'j)).
            slp_left_branch_positive_kernel_joint R left_cutoff
                left_potential left_terminal_value
                (root, (left_arrays, left_terminal)) *
              slp_left_branch_positive_kernel_joint R right_cutoff
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
            \<partial>lborel \<partial>lborel \<partial>lborel) =
      (\<integral>\<^sup>+ left_output.
        slp_left_positive_output_density R left_cutoff left_potential
            (\<lambda>x. ennreal (norm (left_terminal_value x)))
            CARD('i) root left_output *
          slp_right_positive_output_density R right_cutoff right_potential
            (\<lambda>x. ennreal (norm (right_terminal_value x)))
            CARD('j) root (center + root - left_output)
        \<partial>lborel)"
proof -
  let ?left_pairs =
    "\<lambda>left_arrays :: (slp_point^'i) \<times> (slp_point^'i).
      slp_finite_branch_pair_list
        (\<lambda>i. fst left_arrays $ i)
        (\<lambda>i. snd left_arrays $ i)"
  let ?right_pairs =
    "\<lambda>right_arrays :: (slp_point^'j) \<times> (slp_point^'j).
      slp_finite_branch_pair_list
        (\<lambda>i. fst right_arrays $ i)
        (\<lambda>i. snd right_arrays $ i)"
  let ?left_output =
    "\<lambda>left_arrays left_terminal.
      slp_left_branch_output (?left_pairs left_arrays) left_terminal"
  let ?left_kernel =
    "\<lambda>left_arrays left_terminal.
      slp_left_branch_positive_kernel_joint R left_cutoff left_potential
        left_terminal_value (root, (left_arrays, left_terminal))"
  let ?right_kernel =
    "\<lambda>left_arrays left_terminal right_arrays.
      slp_left_branch_positive_kernel_joint R right_cutoff right_potential
        right_terminal_value
        (root, (right_arrays,
          center + root - ?left_output left_arrays left_terminal -
            slp_right_branch_output (?right_pairs right_arrays) 0))"
  let ?left_weight =
    "\<lambda>x. ennreal (norm (left_terminal_value x))"
  let ?right_weight =
    "\<lambda>x. ennreal (norm (right_terminal_value x))"
  let ?right_density =
    "slp_positive_output_density R right_cutoff right_potential
      ?right_weight CARD('j)"
  let ?output_test =
    "\<lambda>left_output.
      ?right_density root (center + root - left_output)"
  have left_weight_measurable[measurable]:
      "?left_weight \<in> borel_measurable lborel"
    by measurable
  have right_weight_measurable[measurable]:
      "?right_weight \<in> borel_measurable lborel"
    by measurable
  have right_density_output_measurable:
      "?right_density root \<in> borel_measurable lborel"
    by (rule slp_positive_output_density_output_measurable[OF
          right_cutoff_measurable right_potential_measurable
          right_weight_measurable])
  have affine_output_measurable:
      "(\<lambda>left_output. center + root - left_output)
        \<in> measurable lborel lborel"
    apply (simp only: measurable_lborel1 measurable_lborel2)
    by (rule borel_measurable_continuous_onI) (intro continuous_intros)
  have output_test_measurable[measurable]:
      "?output_test \<in> borel_measurable lborel"
    using measurable_comp[OF affine_output_measurable
      right_density_output_measurable]
    by (simp only: comp_def)
  have right_joint_kernel_measurable:
      "(slp_left_branch_positive_kernel_joint R right_cutoff right_potential
          right_terminal_value ::
        'j slp_left_branch_finite_coordinates \<Rightarrow> ennreal)
        \<in> borel_measurable lborel"
    by (rule slp_left_branch_positive_kernel_joint_measurable[OF
          right_cutoff_measurable right_potential_measurable
          right_terminal_measurable])
  have right_arrays_to_coordinates_measurable:
      "(\<lambda>right_arrays :: (slp_point^'j) \<times> (slp_point^'j).
        (0, (right_arrays, 0)) :: 'j slp_left_branch_finite_coordinates)
        \<in> measurable lborel lborel"
    apply (simp only: measurable_lborel1 measurable_lborel2)
    by (rule borel_measurable_continuous_onI) (intro continuous_intros)
  have right_branch_output_left_measurable:
      "(\<lambda>right_arrays.
        slp_left_branch_output (?right_pairs right_arrays) 0)
        \<in> borel_measurable lborel"
    using measurable_comp[OF right_arrays_to_coordinates_measurable
      slp_left_branch_finite_output_measurable]
    by (simp only: comp_def prod.sel)
  have right_branch_output_measurable[measurable]:
      "(\<lambda>right_arrays.
        slp_right_branch_output (?right_pairs right_arrays) 0)
        \<in> borel_measurable lborel"
    using right_branch_output_left_measurable
    by (simp only: slp_left_branch_output_eq_right)
  have right_terminal_borel_measurable:
      "(\<lambda>right_arrays.
        center + root - ?left_output left_arrays left_terminal -
          slp_right_branch_output (?right_pairs right_arrays) 0)
        \<in> borel_measurable lborel"
    for left_arrays left_terminal
    by measurable
  have right_terminal_map_measurable:
      "(\<lambda>right_arrays.
        center + root - ?left_output left_arrays left_terminal -
          slp_right_branch_output (?right_pairs right_arrays) 0)
        \<in> measurable lborel lborel"
    for left_arrays left_terminal
    using right_terminal_borel_measurable[of left_arrays left_terminal]
    by (simp only: measurable_lborel1)
  have right_arrays_identity_measurable:
      "(\<lambda>right_arrays :: (slp_point^'j) \<times> (slp_point^'j).
        right_arrays) \<in> measurable lborel lborel"
    by measurable
  have right_inner_coordinates_measurable:
      "(\<lambda>right_arrays.
        (right_arrays,
          center + root - ?left_output left_arrays left_terminal -
            slp_right_branch_output (?right_pairs right_arrays) 0))
        \<in> measurable lborel lborel"
    for left_arrays left_terminal
  proof -
    note raw = measurable_Pair[OF right_arrays_identity_measurable
      right_terminal_map_measurable[of left_arrays left_terminal]]
    show ?thesis
      using raw by (simp only: lborel_prod)
  qed
  have root_constant_measurable:
      "(\<lambda>_ :: (slp_point^'j) \<times> (slp_point^'j). root)
        \<in> measurable lborel lborel"
    by measurable
  have right_coordinates_measurable:
      "((\<lambda>right_arrays.
        (root, (right_arrays,
          center + root - ?left_output left_arrays left_terminal -
            slp_right_branch_output (?right_pairs right_arrays) 0))) ::
          ((slp_point^'j) \<times> (slp_point^'j)) \<Rightarrow>
            'j slp_left_branch_finite_coordinates)
        \<in> measurable lborel lborel"
    for left_arrays left_terminal
  proof -
    note raw = measurable_Pair[OF root_constant_measurable
      right_inner_coordinates_measurable[of left_arrays left_terminal]]
    show ?thesis
      using raw by (simp only: lborel_prod)
  qed
  have right_kernel_measurable:
      "?right_kernel left_arrays left_terminal \<in> borel_measurable lborel"
    for left_arrays left_terminal
    using measurable_comp[OF
      right_coordinates_measurable[of left_arrays left_terminal]
      right_joint_kernel_measurable]
    by (simp only: comp_def)
  have identify_right_density:
      "nn_integral lborel (?right_kernel left_arrays left_terminal) =
        ?output_test (?left_output left_arrays left_terminal)"
    for left_arrays left_terminal
    using slp_left_branch_positive_kernel_joint_fixed_output_integral[
      where R = R and cutoff = right_cutoff and potential = right_potential
        and terminal_value = right_terminal_value and origin = root
        and target = "center + root -
          ?left_output left_arrays left_terminal" and 'i = 'j,
      OF right_cutoff_measurable right_potential_measurable
        right_terminal_measurable]
    by (simp only: slp_left_branch_output_eq_right split_beta'
        prod.sel prod.collapse)
  have integrate_right:
      "nn_integral lborel (\<lambda>right_arrays.
          ?left_kernel left_arrays left_terminal *
            ?right_kernel left_arrays left_terminal right_arrays) =
        ?left_kernel left_arrays left_terminal *
          ?output_test (?left_output left_arrays left_terminal)"
    for left_arrays left_terminal
  proof -
    note pulled = nn_integral_cmult[
      OF right_kernel_measurable[of left_arrays left_terminal],
      where c = "?left_kernel left_arrays left_terminal"]
    show ?thesis
      using pulled identify_right_density[of left_arrays left_terminal]
      by simp
  qed
  have after_right:
      "nn_integral lborel (\<lambda>left_arrays.
          nn_integral lborel (\<lambda>left_terminal.
            nn_integral lborel (\<lambda>right_arrays.
              ?left_kernel left_arrays left_terminal *
                ?right_kernel left_arrays left_terminal right_arrays))) =
        nn_integral lborel (\<lambda>left_arrays.
          nn_integral lborel (\<lambda>left_terminal.
            ?left_kernel left_arrays left_terminal *
              ?output_test (?left_output left_arrays left_terminal)))"
    apply (rule nn_integral_cong)
    apply (rule nn_integral_cong)
    by (simp only: integrate_right)
  note left_pairing =
    slp_left_branch_positive_kernel_joint_output_density_pairing[
      where R = R and cutoff = left_cutoff and potential = left_potential
        and terminal_value = left_terminal_value and output_test = ?output_test
        and root = root and 'i = 'i,
      OF left_cutoff_measurable left_potential_measurable
        left_terminal_measurable output_test_measurable]
  show ?thesis
    using trans[OF after_right left_pairing]
    unfolding slp_left_positive_output_density_def
      slp_right_positive_output_density_def
    by (simp add: mult.commute)
qed

end
