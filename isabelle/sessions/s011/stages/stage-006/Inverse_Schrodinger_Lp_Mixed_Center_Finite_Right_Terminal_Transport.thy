theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Right_Terminal_Transport
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_006.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Positive_Fiber_Mass"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Affine_Output_Transport"
begin

section \<open>Finite mixed right-terminal translation\<close>

theorem slp_mixed_center_finite_right_kernel_center_transport:
  fixes coordinates ::
      "('i::finite, 'j::finite) slp_mixed_center_finite_coordinates"
  assumes cutoff_measurable[measurable]:
      "right_cutoff \<in> borel_measurable lborel"
    and potential_measurable[measurable]:
      "right_potential \<in> borel_measurable lborel"
  shows
    "nn_integral lborel (\<lambda>center.
        slp_left_branch_positive_kernel_joint R right_cutoff right_potential
          (\<lambda>_. 1)
          (snd (slp_mixed_center_finite_inserted_coordinates
            center coordinates))) =
      nn_integral lborel (\<lambda>terminal.
        slp_left_branch_positive_kernel_joint R right_cutoff right_potential
          (\<lambda>_. 1)
          (fst coordinates, (snd (snd coordinates), terminal)))"
proof -
  let ?terminal_kernel =
    "\<lambda>terminal.
      slp_left_branch_positive_kernel_joint R right_cutoff right_potential
        (\<lambda>_. 1)
        (fst coordinates, (snd (snd coordinates), terminal))"
  have terminal_insert_measurable:
      "(\<lambda>terminal.
        (fst coordinates, (snd (snd coordinates), terminal)))
        \<in> measurable lborel lborel"
    apply (simp only: measurable_lborel1 measurable_lborel2)
    by (rule borel_measurable_continuous_onI) (intro continuous_intros)
  have joint_kernel_measurable:
      "(slp_left_branch_positive_kernel_joint R right_cutoff right_potential
          (\<lambda>_. 1) ::
        'j slp_left_branch_finite_coordinates \<Rightarrow> ennreal)
        \<in> borel_measurable lborel"
    by (rule slp_left_branch_positive_kernel_joint_measurable[OF
          cutoff_measurable potential_measurable]) measurable
  have terminal_kernel_measurable:
      "?terminal_kernel \<in> borel_measurable lborel"
    using measurable_comp[OF terminal_insert_measurable
      joint_kernel_measurable]
    by (simp only: comp_def)
  let ?shift =
    "fst coordinates -
      slp_left_branch_output
        (slp_finite_branch_pair_list
          (\<lambda>i. fst (fst (fst (snd coordinates))) $ i)
          (\<lambda>i. snd (fst (fst (snd coordinates))) $ i))
        (snd (fst (snd coordinates))) -
      slp_right_branch_output
        (slp_finite_branch_pair_list
          (\<lambda>i. fst (snd (snd coordinates)) $ i)
          (\<lambda>i. snd (snd (snd coordinates)) $ i))
        0"
  have translated:
      "nn_integral lborel (\<lambda>center. ?terminal_kernel (?shift + center)) =
        nn_integral lborel ?terminal_kernel"
    by (rule slp_nn_integral_translate[OF terminal_kernel_measurable])
  show ?thesis
    using translated
    unfolding slp_mixed_center_finite_inserted_coordinates_def
      slp_mixed_center_finite_right_terminal_def
    by (simp add: algebra_simps)
qed

end
