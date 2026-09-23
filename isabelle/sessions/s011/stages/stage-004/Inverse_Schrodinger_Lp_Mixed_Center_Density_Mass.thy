theory Inverse_Schrodinger_Lp_Mixed_Center_Density_Mass
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Mixed_Center_Density"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Affine_Output_Transport"
begin

section \<open>Global mass of the positive mixed center density\<close>

theorem slp_mixed_center_density_mass:
  assumes cutoff_measurable[measurable]:
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
        slp_mixed_center_density R cutoff left_potential right_potential
          left_terminal_weight right_terminal_weight left_order right_order
          root_weight center
        \<partial>lborel) =
      (\<integral>\<^sup>+ root.
        ennreal (Real_Vector_Spaces.norm (root_weight root)) *
        (\<integral>\<^sup>+ left_output.
          slp_left_positive_output_density R cutoff left_potential
            left_terminal_weight left_order root left_output
          \<partial>lborel) *
        (\<integral>\<^sup>+ right_output.
          slp_right_positive_output_density R cutoff right_potential
            right_terminal_weight right_order root right_output
          \<partial>lborel)
        \<partial>lborel)"
proof -
  let ?left =
    "slp_left_positive_output_density R cutoff left_potential
      left_terminal_weight left_order"
  let ?right =
    "slp_right_positive_output_density R cutoff right_potential
      right_terminal_weight right_order"
  let ?root_norm =
    "\<lambda>root. ennreal (Real_Vector_Spaces.norm (root_weight root))"
  let ?integrand =
    "\<lambda>center root left_output.
      ?root_norm root * ?left root left_output *
        ?right root (center + root - left_output)"
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
  have left_slice[measurable]:
      "?left root \<in> borel_measurable lborel" for root
    using left_joint by measurable
  have right_slice[measurable]:
      "?right root \<in> borel_measurable lborel" for root
    using right_joint by measurable
  have expand_left:
      "(\<integral>\<^sup>+ center.
          slp_mixed_center_density R cutoff left_potential right_potential
            left_terminal_weight right_terminal_weight left_order right_order
            root_weight center
          \<partial>lborel) =
        (\<integral>\<^sup>+ center. \<integral>\<^sup>+ root.
          \<integral>\<^sup>+ left_output. ?integrand center root left_output
          \<partial>lborel \<partial>lborel \<partial>lborel)"
    unfolding slp_mixed_center_density_def by simp
  have center_root_measurable:
      "case_prod (\<lambda>center root.
        \<integral>\<^sup>+ left_output. ?integrand center root left_output
          \<partial>lborel) \<in>
        borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by measurable
  have swap_center_root:
      "(\<integral>\<^sup>+ center. \<integral>\<^sup>+ root.
          \<integral>\<^sup>+ left_output. ?integrand center root left_output
          \<partial>lborel \<partial>lborel \<partial>lborel) =
        (\<integral>\<^sup>+ root. \<integral>\<^sup>+ center.
          \<integral>\<^sup>+ left_output. ?integrand center root left_output
          \<partial>lborel \<partial>lborel \<partial>lborel)"
    using lborel_pair.Fubini'[OF center_root_measurable] by simp
  have swap_center_left:
      "(\<integral>\<^sup>+ center. \<integral>\<^sup>+ left_output.
          ?integrand center root left_output
          \<partial>lborel \<partial>lborel) =
        (\<integral>\<^sup>+ left_output. \<integral>\<^sup>+ center.
          ?integrand center root left_output
          \<partial>lborel \<partial>lborel)" for root
  proof -
    have measurable_pair:
        "case_prod (\<lambda>center left_output.
          ?integrand center root left_output) \<in>
          borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
      by measurable
    show ?thesis
      using lborel_pair.Fubini'[OF measurable_pair] by simp
  qed
  have reorder:
      "(\<integral>\<^sup>+ center. \<integral>\<^sup>+ root.
          \<integral>\<^sup>+ left_output. ?integrand center root left_output
          \<partial>lborel \<partial>lborel \<partial>lborel) =
        (\<integral>\<^sup>+ root. \<integral>\<^sup>+ left_output.
          \<integral>\<^sup>+ center. ?integrand center root left_output
          \<partial>lborel \<partial>lborel \<partial>lborel)"
  proof -
    have swap_inner:
        "(\<integral>\<^sup>+ root. \<integral>\<^sup>+ center.
            \<integral>\<^sup>+ left_output. ?integrand center root left_output
            \<partial>lborel \<partial>lborel \<partial>lborel) =
          (\<integral>\<^sup>+ root. \<integral>\<^sup>+ left_output.
            \<integral>\<^sup>+ center. ?integrand center root left_output
            \<partial>lborel \<partial>lborel \<partial>lborel)"
      by (rule nn_integral_cong) (rule swap_center_left)
    show ?thesis
      using swap_center_root swap_inner by simp
  qed
  have translate_right:
      "(\<integral>\<^sup>+ center.
          ?right root (center + root - left_output) \<partial>lborel) =
        (\<integral>\<^sup>+ right_output.
          ?right root right_output \<partial>lborel)"
      for root left_output
  proof -
    have invariant:
        "(\<integral>\<^sup>+ center.
            ?right root ((root - left_output) + center) \<partial>lborel) =
          (\<integral>\<^sup>+ right_output.
            ?right root right_output \<partial>lborel)"
      by (rule slp_nn_integral_translate[OF right_slice])
    show ?thesis
      using invariant by (simp add: algebra_simps)
  qed
  have integrate_center:
      "(\<integral>\<^sup>+ center. ?integrand center root left_output
          \<partial>lborel) =
        ?root_norm root * ?left root left_output *
          (\<integral>\<^sup>+ right_output.
            ?right root right_output \<partial>lborel)"
      for root left_output
  proof -
    have right_comp_measurable:
        "(\<lambda>center. ?right root (center + root - left_output))
          \<in> borel_measurable lborel"
      by measurable
    have pull:
        "(\<integral>\<^sup>+ center.
            (?root_norm root * ?left root left_output) *
              ?right root (center + root - left_output) \<partial>lborel) =
          (?root_norm root * ?left root left_output) *
            (\<integral>\<^sup>+ center.
              ?right root (center + root - left_output) \<partial>lborel)"
      by (rule nn_integral_cmult[OF right_comp_measurable])
    show ?thesis
      using pull translate_right by (simp add: mult.assoc)
  qed
  have integrate_left:
      "(\<integral>\<^sup>+ left_output.
          ?root_norm root * ?left root left_output *
            (\<integral>\<^sup>+ right_output.
              ?right root right_output \<partial>lborel)
          \<partial>lborel) =
        ?root_norm root *
          (\<integral>\<^sup>+ left_output.
            ?left root left_output \<partial>lborel) *
          (\<integral>\<^sup>+ right_output.
            ?right root right_output \<partial>lborel)" for root
  proof -
    let ?right_mass =
      "\<integral>\<^sup>+ right_output. ?right root right_output \<partial>lborel"
    have pull:
        "(\<integral>\<^sup>+ left_output.
            (?root_norm root * ?right_mass) * ?left root left_output
            \<partial>lborel) =
          (?root_norm root * ?right_mass) *
            (\<integral>\<^sup>+ left_output.
              ?left root left_output \<partial>lborel)"
      by (rule nn_integral_cmult[OF left_slice])
    show ?thesis
      using pull
      by (simp add: mult.assoc mult.commute mult.left_commute)
  qed
  have integrate_all:
      "(\<integral>\<^sup>+ root. \<integral>\<^sup>+ left_output.
          \<integral>\<^sup>+ center. ?integrand center root left_output
          \<partial>lborel \<partial>lborel \<partial>lborel) =
        (\<integral>\<^sup>+ root.
          ?root_norm root *
          (\<integral>\<^sup>+ left_output.
            ?left root left_output \<partial>lborel) *
          (\<integral>\<^sup>+ right_output.
            ?right root right_output \<partial>lborel)
          \<partial>lborel)"
  proof (rule nn_integral_cong)
    fix root
    show
      "(\<integral>\<^sup>+ left_output. \<integral>\<^sup>+ center.
          ?integrand center root left_output
          \<partial>lborel \<partial>lborel) =
        ?root_norm root *
          (\<integral>\<^sup>+ left_output.
            ?left root left_output \<partial>lborel) *
          (\<integral>\<^sup>+ right_output.
            ?right root right_output \<partial>lborel)"
      by (simp only: integrate_center integrate_left)
  qed
  show ?thesis
    using expand_left reorder integrate_all by simp
qed

end
