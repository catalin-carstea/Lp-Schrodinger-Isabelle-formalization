theory Inverse_Schrodinger_Lp_Mixed_Center_Density_Pairing_Nested_Branches
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Mixed_Center_Density_Pairing_Right_Branch"
begin

section \<open>Nested branch-functional form of the mixed center pairing\<close>

theorem slp_mixed_center_density_pairing_nested_branches:
  assumes center_test_measurable[measurable]:
      "center_test \<in> borel_measurable lborel"
    and cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and left_potential_measurable[measurable]:
      "left_potential \<in> borel_measurable lborel"
    and right_potential_measurable[measurable]:
      "right_potential \<in> borel_measurable lborel"
    and left_terminal_measurable[measurable]:
      "left_terminal_weight \<in> borel_measurable lborel"
    and right_terminal_measurable[measurable]:
      "right_terminal_weight \<in> borel_measurable lborel"
    and root_weight_measurable[measurable]:
      "root_weight \<in> borel_measurable lborel"
  shows
    "(\<integral>\<^sup>+ center.
        center_test center *
        slp_mixed_center_density R cutoff left_potential right_potential
          left_terminal_weight right_terminal_weight left_order right_order
          root_weight center
        \<partial>lborel) =
      (\<integral>\<^sup>+ root.
        ennreal (Real_Vector_Spaces.norm (root_weight root)) *
        slp_positive_branch_functional R cutoff left_potential
          left_terminal_weight left_order root
          (\<lambda>left_output.
            slp_positive_branch_functional R cutoff right_potential
              right_terminal_weight right_order root
              (\<lambda>right_output.
                center_test (- root + left_output + right_output)))
        \<partial>lborel)"
proof -
  let ?left_density =
    "slp_left_positive_output_density R cutoff left_potential
      left_terminal_weight left_order"
  let ?right_density =
    "slp_right_positive_output_density R cutoff right_potential
      right_terminal_weight right_order"
  let ?right_functional =
    "\<lambda>root left_output.
      slp_positive_branch_functional R cutoff right_potential
        right_terminal_weight right_order root
        (\<lambda>right_output.
          center_test (- root + left_output + right_output))"
  let ?root_norm =
    "\<lambda>root. ennreal (Real_Vector_Spaces.norm (root_weight root))"
  have left_density_joint[measurable]:
      "case_prod ?left_density \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by (rule slp_left_positive_output_density_joint_measurable[OF
          cutoff_measurable left_potential_measurable
          left_terminal_measurable])
  have right_density_joint[measurable]:
      "case_prod ?right_density \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by (rule slp_right_positive_output_density_joint_measurable[OF
          cutoff_measurable right_potential_measurable
          right_terminal_measurable])
  have right_expansion:
      "?right_functional root left_output =
        (\<integral>\<^sup>+ right_output.
          center_test (- root + left_output + right_output) *
          ?right_density root right_output \<partial>lborel)"
    for root left_output
    using slp_right_positive_output_density_pushforward[OF
        cutoff_measurable right_potential_measurable
        right_terminal_measurable, of
        "\<lambda>right_output.
          center_test (- root + left_output + right_output)" R right_order root]
    by (simp add: measurable)
  have nested_test_measurable[measurable]:
      "(\<lambda>left_output. ?right_functional root left_output)
        \<in> borel_measurable lborel" for root
  proof -
    have density_integral_measurable:
        "(\<lambda>left_output.
          \<integral>\<^sup>+ right_output.
            center_test (- root + left_output + right_output) *
            ?right_density root right_output \<partial>lborel)
          \<in> borel_measurable lborel"
      by measurable
    show ?thesis
      using density_integral_measurable
      by (simp only: right_expansion)
  qed
  have left_collapse:
      "(\<integral>\<^sup>+ left_output.
          ?right_functional root left_output *
          ?left_density root left_output \<partial>lborel) =
        slp_positive_branch_functional R cutoff left_potential
          left_terminal_weight left_order root
          (\<lambda>left_output. ?right_functional root left_output)" for root
    by (rule slp_left_positive_output_density_pushforward[OF
          cutoff_measurable left_potential_measurable
          left_terminal_measurable nested_test_measurable])
  have collapse_under_root:
      "(\<integral>\<^sup>+ left_output.
          ?root_norm root * ?left_density root left_output *
            ?right_functional root left_output \<partial>lborel) =
        ?root_norm root *
          slp_positive_branch_functional R cutoff left_potential
            left_terminal_weight left_order root
            (\<lambda>left_output. ?right_functional root left_output)" for root
  proof -
    have pair_measurable:
        "(\<lambda>left_output.
          ?right_functional root left_output *
            ?left_density root left_output) \<in> borel_measurable lborel"
      by measurable
    have pull_root:
        "(\<integral>\<^sup>+ left_output.
          ?root_norm root *
            (?right_functional root left_output *
              ?left_density root left_output) \<partial>lborel) =
        ?root_norm root *
          (\<integral>\<^sup>+ left_output.
            ?right_functional root left_output *
              ?left_density root left_output \<partial>lborel)"
      by (rule nn_integral_cmult[OF pair_measurable])
    show ?thesis
      using pull_root left_collapse
      by (simp add: mult.assoc mult.commute mult.left_commute)
  qed
  note pairing = slp_mixed_center_density_pairing_right_branch[OF
      center_test_measurable cutoff_measurable
      left_potential_measurable right_potential_measurable
      left_terminal_measurable right_terminal_measurable
      root_weight_measurable]
  show ?thesis
    using pairing
    by (simp only: collapse_under_root)
qed

end
