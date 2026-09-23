theory Inverse_Schrodinger_Lp_Mixed_Center_Density_Pairing_Right_Branch
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Mixed_Center_Density_Pairing"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_Output_Pushforward_Aliases"
begin

section \<open>Right-branch collapse of the mixed center pairing\<close>

theorem slp_mixed_center_density_pairing_right_branch:
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
        slp_positive_branch_functional R cutoff right_potential
          right_terminal_weight right_order root
          (\<lambda>right_output.
            center_test (- root + left_output + right_output))
        \<partial>lborel \<partial>lborel)"
proof -
  have pairing:
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
    by (rule slp_mixed_center_density_pairing[OF
          center_test_measurable cutoff_measurable
          left_potential_measurable right_potential_measurable
          left_terminal_measurable right_terminal_measurable
          root_weight_measurable])
  have collapse:
      "(\<integral>\<^sup>+ right_output.
          center_test (- root + left_output + right_output) *
          slp_right_positive_output_density R cutoff right_potential
            right_terminal_weight right_order root right_output
          \<partial>lborel) =
        slp_positive_branch_functional R cutoff right_potential
          right_terminal_weight right_order root
          (\<lambda>right_output.
            center_test (- root + left_output + right_output))"
    for root left_output
  proof (rule slp_right_positive_output_density_pushforward[OF
        cutoff_measurable right_potential_measurable
        right_terminal_measurable])
    show "(\<lambda>right_output.
        center_test (- root + left_output + right_output))
      \<in> borel_measurable lborel"
      by measurable
  qed
  show ?thesis
    using pairing
    by (simp only: collapse)
qed

end
