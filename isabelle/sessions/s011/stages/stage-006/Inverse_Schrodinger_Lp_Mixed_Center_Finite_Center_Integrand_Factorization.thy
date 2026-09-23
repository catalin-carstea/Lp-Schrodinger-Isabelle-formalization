theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Center_Integrand_Factorization
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_006.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Right_Terminal_Transport"
begin

section \<open>Finite mixed center-integrand factorization\<close>

theorem slp_mixed_center_finite_positive_integrand_center_factorization:
  fixes coordinates ::
      "('i::finite, 'j::finite) slp_mixed_center_finite_coordinates"
  assumes cutoff_measurable[measurable]:
      "right_cutoff \<in> borel_measurable lborel"
    and potential_measurable[measurable]:
      "right_potential \<in> borel_measurable lborel"
  shows
    "nn_integral lborel (\<lambda>center.
        ennreal (cmod (root_weight (fst coordinates))) *
          slp_left_branch_positive_kernel_joint R left_cutoff left_potential
            (\<lambda>_. 1) (fst coordinates, fst (snd coordinates)) *
          slp_left_branch_positive_kernel_joint R right_cutoff right_potential
            (\<lambda>_. 1)
            (snd (slp_mixed_center_finite_inserted_coordinates
              center coordinates))) =
      ennreal (cmod (root_weight (fst coordinates))) *
        slp_left_branch_positive_kernel_joint R left_cutoff left_potential
          (\<lambda>_. 1) (fst coordinates, fst (snd coordinates)) *
        nn_integral lborel (\<lambda>terminal.
          slp_left_branch_positive_kernel_joint R right_cutoff right_potential
            (\<lambda>_. 1)
            (fst coordinates, (snd (snd coordinates), terminal)))"
proof -
  let ?scale =
    "ennreal (cmod (root_weight (fst coordinates))) *
      slp_left_branch_positive_kernel_joint R left_cutoff left_potential
        (\<lambda>_. 1) (fst coordinates, fst (snd coordinates))"
  let ?right_center =
    "\<lambda>center.
      slp_left_branch_positive_kernel_joint R right_cutoff right_potential
        (\<lambda>_. 1)
        (snd (slp_mixed_center_finite_inserted_coordinates
          center coordinates))"
  have right_coordinates_measurable:
      "(\<lambda>center.
        snd (slp_mixed_center_finite_inserted_coordinates
          center coordinates)) \<in> measurable lborel lborel"
    apply (simp only: measurable_lborel1 measurable_lborel2)
    apply (rule borel_measurable_continuous_onI)
    unfolding slp_mixed_center_finite_inserted_coordinates_def
      slp_mixed_center_finite_right_terminal_def
    by (intro continuous_intros)
  have joint_kernel_measurable:
      "(slp_left_branch_positive_kernel_joint R right_cutoff right_potential
          (\<lambda>_. 1) ::
        'j slp_left_branch_finite_coordinates \<Rightarrow> ennreal)
        \<in> borel_measurable lborel"
    by (rule slp_left_branch_positive_kernel_joint_measurable[OF
          cutoff_measurable potential_measurable]) measurable
  have right_center_measurable:
      "?right_center \<in> borel_measurable lborel"
    using measurable_comp[OF right_coordinates_measurable
      joint_kernel_measurable]
    by (simp only: comp_def)
  have pull_scale:
      "nn_integral lborel (\<lambda>center. ?scale * ?right_center center) =
        ?scale * nn_integral lborel ?right_center"
    by (rule nn_integral_cmult[OF right_center_measurable])
  have terminal_transport:
      "nn_integral lborel ?right_center =
        nn_integral lborel (\<lambda>terminal.
          slp_left_branch_positive_kernel_joint R right_cutoff right_potential
            (\<lambda>_. 1)
            (fst coordinates, (snd (snd coordinates), terminal)))"
    by (rule slp_mixed_center_finite_right_kernel_center_transport[OF
          cutoff_measurable potential_measurable])
  show ?thesis
    using pull_scale terminal_transport by simp
qed

end
