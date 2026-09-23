theory Inverse_Schrodinger_Lp_One_Sided_Finite_Unit_Inner_Mass_Split
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_006.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Positive_Mass_Tonelli"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_One_Sided_Finite_Positive_Inner_Mass"
begin

section \<open>Unit finite positive inner-mass product split\<close>

theorem slp_left_branch_positive_inner_mass_finite_unit_split:
  fixes root :: slp_point
    and cutoff potential :: "slp_point \<Rightarrow> complex"
  assumes cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and potential_measurable[measurable]:
      "potential \<in> borel_measurable lborel"
  shows
    "slp_left_branch_positive_inner_mass_finite TYPE('i::finite) R cutoff
        potential (\<lambda>_. 1) (\<lambda>_. 1) root =
      nn_integral lborel (\<lambda>branch_arrays ::
          (slp_point^'i) \<times> (slp_point^'i).
        nn_integral lborel (\<lambda>terminal.
          slp_left_branch_positive_kernel_joint R cutoff potential
            (\<lambda>_. 1) (root, (branch_arrays, terminal))))"
proof -
  let ?kernel =
    "\<lambda>branch_coordinates ::
        ((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point.
      slp_left_branch_positive_kernel_joint R cutoff potential
        (\<lambda>_. 1) (root, branch_coordinates)"
  have pair_root_measurable:
      "(\<lambda>branch_coordinates ::
          ((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point.
        (root, branch_coordinates)) \<in> measurable lborel lborel"
    apply (simp only: measurable_lborel1 measurable_lborel2)
    by (rule borel_measurable_continuous_onI) (intro continuous_intros)
  have joint_kernel_measurable:
      "(slp_left_branch_positive_kernel_joint R cutoff potential
          (\<lambda>_. 1) ::
        'i slp_left_branch_finite_coordinates \<Rightarrow> ennreal)
        \<in> borel_measurable lborel"
    by (rule slp_left_branch_positive_kernel_joint_measurable[OF
          cutoff_measurable potential_measurable]) measurable
  have kernel_measurable:
      "?kernel \<in> borel_measurable lborel"
    using measurable_comp[OF pair_root_measurable joint_kernel_measurable]
    by (simp only: comp_def)
  have kernel_product_measurable:
      "?kernel \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    using kernel_measurable by (simp only: lborel_prod)
  have split:
      "nn_integral lborel ?kernel =
        nn_integral lborel (\<lambda>branch_arrays.
          nn_integral lborel (\<lambda>terminal.
            ?kernel (branch_arrays, terminal)))"
  proof -
    note raw = lborel.nn_integral_fst[OF kernel_product_measurable]
    show ?thesis
      using raw[symmetric] by (simp only: lborel_prod)
  qed
  show ?thesis
    unfolding slp_left_branch_positive_inner_mass_finite_def
    using split by simp
qed

end
