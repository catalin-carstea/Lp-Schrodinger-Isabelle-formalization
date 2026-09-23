theory Inverse_Schrodinger_Lp_One_Sided_Finite_Unit_Inner_Mass_Measurable
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_006.Inverse_Schrodinger_Lp_One_Sided_Finite_Unit_Inner_Mass_Split"
begin

section \<open>Measurability of the unit finite positive inner mass\<close>

theorem slp_left_branch_positive_inner_mass_finite_unit_measurable:
  fixes cutoff potential :: "slp_point \<Rightarrow> complex"
  assumes cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and potential_measurable[measurable]:
      "potential \<in> borel_measurable lborel"
  shows
    "(\<lambda>root.
      slp_left_branch_positive_inner_mass_finite TYPE('i::finite) R cutoff
        potential (\<lambda>_. 1) (\<lambda>_. 1) root)
      \<in> borel_measurable lborel"
proof -
  let ?kernel =
    "slp_left_branch_positive_kernel_joint R cutoff potential (\<lambda>_. 1) ::
      'i slp_left_branch_finite_coordinates \<Rightarrow> ennreal"
  have kernel_measurable:
      "?kernel \<in> borel_measurable lborel"
    by (rule slp_left_branch_positive_kernel_joint_measurable[OF
          cutoff_measurable potential_measurable]) measurable
  have kernel_product_measurable:
      "?kernel \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    using kernel_measurable by (simp only: lborel_prod)
  have parameter_integral_measurable:
      "(\<lambda>root.
        nn_integral lborel (\<lambda>branch_coordinates.
          ?kernel (root, branch_coordinates)))
        \<in> borel_measurable lborel"
    by (rule lborel.borel_measurable_nn_integral_fst[OF
          kernel_product_measurable])
  show ?thesis
    unfolding slp_left_branch_positive_inner_mass_finite_def
    using parameter_integral_measurable by simp
qed

end
