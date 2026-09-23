theory Inverse_Schrodinger_Lp_Mixed_Center_Density_Pairing
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Mixed_Center_Density_Mass"
begin

section \<open>Nonnegative test pairing for the mixed center density\<close>

theorem slp_mixed_center_density_pairing:
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
      (\<integral>\<^sup>+ root. \<integral>\<^sup>+ left_output.
        ennreal (Real_Vector_Spaces.norm (root_weight root)) *
        slp_left_positive_output_density R cutoff left_potential
          left_terminal_weight left_order root left_output *
        (\<integral>\<^sup>+ right_output.
          center_test (- root + left_output + right_output) *
          slp_right_positive_output_density R cutoff right_potential
            right_terminal_weight right_order root right_output
          \<partial>lborel)
        \<partial>lborel \<partial>lborel)"
proof -
  let ?left =
    "slp_left_positive_output_density R cutoff left_potential
      left_terminal_weight left_order"
  let ?right =
    "slp_right_positive_output_density R cutoff right_potential
      right_terminal_weight right_order"
  let ?root_norm =
    "\<lambda>root. ennreal (Real_Vector_Spaces.norm (root_weight root))"
  let ?block =
    "\<lambda>left_output root.
      ?root_norm root * ?left root left_output"
  have left_joint[measurable]:
      "case_prod ?left \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by (rule slp_left_positive_output_density_joint_measurable[OF
          cutoff_measurable left_potential_measurable
          left_terminal_measurable])
  have right_joint[measurable]:
      "case_prod ?right \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by (rule slp_right_positive_output_density_joint_measurable[OF
          cutoff_measurable right_potential_measurable
          right_terminal_measurable])
  have block_joint[measurable]:
      "case_prod ?block \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by measurable
  have density_reordered:
      "slp_mixed_center_density R cutoff left_potential right_potential
          left_terminal_weight right_terminal_weight left_order right_order
          root_weight center =
        (\<integral>\<^sup>+ left_output. \<integral>\<^sup>+ root.
          ?block left_output root *
            ?right root (center - left_output + root)
          \<partial>lborel \<partial>lborel)" for center
  proof -
    let ?joint =
      "\<lambda>root left_output.
        ?root_norm root * ?left root left_output *
          ?right root (center + root - left_output)"
    have joint_measurable:
        "case_prod ?joint \<in>
          borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
      by measurable
    have swap:
        "(\<integral>\<^sup>+ root. \<integral>\<^sup>+ left_output.
            ?joint root left_output \<partial>lborel \<partial>lborel) =
          (\<integral>\<^sup>+ left_output. \<integral>\<^sup>+ root.
            ?joint root left_output \<partial>lborel \<partial>lborel)"
      using lborel_pair.Fubini'[OF joint_measurable] by simp
    show ?thesis
      unfolding slp_mixed_center_density_def
      using swap by (simp add: algebra_simps mult.assoc)
  qed
  have transport:
      "(\<integral>\<^sup>+ center. center_test center *
          (\<integral>\<^sup>+ left_output. \<integral>\<^sup>+ root.
            ?block left_output root *
              ?right root (center - left_output + root)
            \<partial>lborel \<partial>lborel)
          \<partial>lborel) =
        (\<integral>\<^sup>+ left_output. \<integral>\<^sup>+ root.
          ?block left_output root *
          (\<integral>\<^sup>+ right_output.
            center_test (right_output + left_output - root) *
              ?right root right_output \<partial>lborel)
          \<partial>lborel \<partial>lborel)"
    by (rule slp_nn_integral_affine_output_transport[OF
          center_test_measurable block_joint right_joint])
  let ?paired =
    "\<lambda>left_output root.
      ?block left_output root *
      (\<integral>\<^sup>+ right_output.
        center_test (right_output + left_output - root) *
          ?right root right_output \<partial>lborel)"
  have paired_joint[measurable]:
      "case_prod ?paired \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by measurable
  have swap_outer:
      "(\<integral>\<^sup>+ left_output. \<integral>\<^sup>+ root.
          ?paired left_output root \<partial>lborel \<partial>lborel) =
        (\<integral>\<^sup>+ root. \<integral>\<^sup>+ left_output.
          ?paired left_output root \<partial>lborel \<partial>lborel)"
    using lborel_pair.Fubini'[OF paired_joint] by simp
  have paired_normalized:
      "(\<integral>\<^sup>+ root. \<integral>\<^sup>+ left_output.
          ?paired left_output root \<partial>lborel \<partial>lborel) =
        (\<integral>\<^sup>+ root. \<integral>\<^sup>+ left_output.
          ?root_norm root * ?left root left_output *
          (\<integral>\<^sup>+ right_output.
            center_test (- root + left_output + right_output) *
              ?right root right_output \<partial>lborel)
          \<partial>lborel \<partial>lborel)"
    by (intro nn_integral_cong)
      (simp add: algebra_simps mult.assoc)
  show ?thesis
    using transport swap_outer paired_normalized
    by (simp only: density_reordered)
qed

end
