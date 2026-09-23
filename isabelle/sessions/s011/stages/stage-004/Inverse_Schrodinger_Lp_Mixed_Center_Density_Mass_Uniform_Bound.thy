theory Inverse_Schrodinger_Lp_Mixed_Center_Density_Mass_Uniform_Bound
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Mixed_Center_Density_Mass"
begin

section \<open>Uniform branch-mass bound for the mixed center density\<close>

theorem slp_mixed_center_density_mass_uniform_bound:
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
    and left_mass_bound:
      "\<And>root. (\<integral>\<^sup>+ output.
        slp_left_positive_output_density R cutoff left_potential
          left_terminal_weight left_order root output \<partial>lborel)
        \<le> left_bound"
    and right_mass_bound:
      "\<And>root. (\<integral>\<^sup>+ output.
        slp_right_positive_output_density R cutoff right_potential
          right_terminal_weight right_order root output \<partial>lborel)
        \<le> right_bound"
  shows
    "(\<integral>\<^sup>+ center.
        slp_mixed_center_density R cutoff left_potential right_potential
          left_terminal_weight right_terminal_weight left_order right_order
          root_weight center \<partial>lborel) \<le>
      (\<integral>\<^sup>+ root.
        ennreal (Real_Vector_Spaces.norm (root_weight root)) \<partial>lborel) *
      left_bound * right_bound"
proof -
  let ?left_mass =
    "\<lambda>root. \<integral>\<^sup>+ output.
      slp_left_positive_output_density R cutoff left_potential
        left_terminal_weight left_order root output \<partial>lborel"
  let ?right_mass =
    "\<lambda>root. \<integral>\<^sup>+ output.
      slp_right_positive_output_density R cutoff right_potential
        right_terminal_weight right_order root output \<partial>lborel"
  let ?root_norm =
    "\<lambda>root. ennreal (Real_Vector_Spaces.norm (root_weight root))"
  have root_norm_measurable[measurable]:
      "?root_norm \<in> borel_measurable lborel"
    by measurable
  have mass_identity:
      "(\<integral>\<^sup>+ center.
          slp_mixed_center_density R cutoff left_potential right_potential
            left_terminal_weight right_terminal_weight left_order right_order
            root_weight center \<partial>lborel) =
        (\<integral>\<^sup>+ root.
          ?root_norm root * ?left_mass root * ?right_mass root
          \<partial>lborel)"
    by (rule slp_mixed_center_density_mass[OF
          cutoff_measurable left_potential_measurable
          right_potential_measurable left_terminal_measurable
          right_terminal_measurable root_weight_measurable])
  have pointwise_bound:
      "?root_norm root * ?left_mass root * ?right_mass root \<le>
        ?root_norm root * left_bound * right_bound" for root
    by (intro mult_mono left_mass_bound right_mass_bound) simp_all
  have integrate_bound:
      "(\<integral>\<^sup>+ root.
          ?root_norm root * ?left_mass root * ?right_mass root
          \<partial>lborel) \<le>
        (\<integral>\<^sup>+ root.
          ?root_norm root * left_bound * right_bound \<partial>lborel)"
    by (intro nn_integral_mono pointwise_bound)
  have root_left_measurable:
      "(\<lambda>root. ?root_norm root * left_bound)
        \<in> borel_measurable lborel"
    by measurable
  have factor_constants:
      "(\<integral>\<^sup>+ root.
          ?root_norm root * left_bound * right_bound \<partial>lborel) =
        (\<integral>\<^sup>+ root. ?root_norm root \<partial>lborel) *
          left_bound * right_bound"
    by (simp only: nn_integral_multc[OF root_left_measurable]
        nn_integral_multc[OF root_norm_measurable])
  show ?thesis
    using mass_identity integrate_bound factor_constants by simp
qed

end
