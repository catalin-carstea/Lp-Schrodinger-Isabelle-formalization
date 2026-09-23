theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Residual_Measurable
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_005.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Complex_Amplitude"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_One_Sided_Finite_Principal_Integral"
begin

section \<open>Joint measurability of the solved-center mixed residual\<close>

theorem slp_mixed_center_finite_residual_measurable:
  "case_prod (slp_mixed_center_finite_residual ::
      slp_point \<Rightarrow>
        ('i::finite, 'j::finite) slp_mixed_center_finite_coordinates
          \<Rightarrow> real)
    \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
proof -
  let ?inserted =
    "\<lambda>z :: slp_point \<times>
        ('i, 'j) slp_mixed_center_finite_coordinates.
      slp_mixed_center_finite_inserted_coordinates (fst z) (snd z)"
  let ?left_coordinates = "\<lambda>z. fst (?inserted z)"
  let ?right_coordinates = "\<lambda>z. snd (?inserted z)"
  let ?left_branch_residual =
    "\<lambda>(coordinates :: 'i slp_left_branch_finite_coordinates).
      slp_left_branch_residual
        (slp_finite_branch_pair_list
          (\<lambda>i. fst (fst (snd coordinates)) $ i)
          (\<lambda>i. snd (fst (snd coordinates)) $ i))
        (snd (snd coordinates))"
  let ?right_branch_residual =
    "\<lambda>(coordinates :: 'j slp_left_branch_finite_coordinates).
      slp_left_branch_residual
        (slp_finite_branch_pair_list
          (\<lambda>i. fst (fst (snd coordinates)) $ i)
          (\<lambda>i. snd (fst (snd coordinates)) $ i))
        (snd (snd coordinates))"
  let ?left_branch_output =
    "\<lambda>(coordinates :: 'i slp_left_branch_finite_coordinates).
      slp_left_branch_output
        (slp_finite_branch_pair_list
          (\<lambda>i. fst (fst (snd coordinates)) $ i)
          (\<lambda>i. snd (fst (snd coordinates)) $ i))
        (snd (snd coordinates))"
  let ?right_branch_output =
    "\<lambda>(coordinates :: 'j slp_left_branch_finite_coordinates).
      slp_left_branch_output
        (slp_finite_branch_pair_list
          (\<lambda>i. fst (fst (snd coordinates)) $ i)
          (\<lambda>i. snd (fst (snd coordinates)) $ i))
        (snd (snd coordinates))"
  have inserted_measurable:
      "?inserted \<in> borel_measurable lborel"
    by (rule slp_mixed_center_finite_inserted_coordinates_measurable)
  have inserted_product_measurable:
      "?inserted \<in> measurable lborel (lborel \<Otimes>\<^sub>M lborel)"
    using inserted_measurable
    by (simp only: lborel_prod measurable_lborel1)
  have left_coordinates_measurable[measurable]:
      "?left_coordinates \<in> borel_measurable lborel"
    using measurable_compose[OF inserted_product_measurable measurable_fst]
    by (simp add: comp_def measurable_lborel1)
  have right_coordinates_measurable[measurable]:
      "?right_coordinates \<in> borel_measurable lborel"
    using measurable_compose[OF inserted_product_measurable measurable_snd]
    by (simp add: comp_def measurable_lborel1)
  have left_branch_residual_measurable:
      "?left_branch_residual \<in> borel_measurable lborel"
    by (rule slp_left_branch_finite_list_residual_measurable)
  have right_branch_residual_measurable:
      "?right_branch_residual \<in> borel_measurable lborel"
    by (rule slp_left_branch_finite_list_residual_measurable)
  have left_branch_residual_borel_measurable:
      "?left_branch_residual \<in> borel_measurable borel"
    using left_branch_residual_measurable
    by (simp only: measurable_lborel2)
  have right_branch_residual_borel_measurable:
      "?right_branch_residual \<in> borel_measurable borel"
    using right_branch_residual_measurable
    by (simp only: measurable_lborel2)
  have left_residual_measurable[measurable]:
      "(\<lambda>z. ?left_branch_residual (?left_coordinates z))
        \<in> borel_measurable lborel"
    by (rule measurable_compose[OF left_coordinates_measurable
          left_branch_residual_borel_measurable])
  have right_residual_measurable[measurable]:
      "(\<lambda>z. ?right_branch_residual (?right_coordinates z))
        \<in> borel_measurable lborel"
    by (rule measurable_compose[OF right_coordinates_measurable
          right_branch_residual_borel_measurable])
  have left_branch_output_measurable:
      "?left_branch_output \<in> borel_measurable lborel"
    by (rule slp_left_branch_finite_output_measurable)
  have right_branch_output_measurable:
      "?right_branch_output \<in> borel_measurable lborel"
    by (rule slp_left_branch_finite_output_measurable)
  have left_branch_output_borel_measurable:
      "?left_branch_output \<in> borel_measurable borel"
    using left_branch_output_measurable by (simp only: measurable_lborel2)
  have right_branch_output_borel_measurable:
      "?right_branch_output \<in> borel_measurable borel"
    using right_branch_output_measurable by (simp only: measurable_lborel2)
  have left_output_measurable[measurable]:
      "(\<lambda>z. ?left_branch_output (?left_coordinates z))
        \<in> borel_measurable lborel"
    by (rule measurable_compose[OF left_coordinates_measurable
          left_branch_output_borel_measurable])
  have right_output_measurable[measurable]:
      "(\<lambda>z. ?right_branch_output (?right_coordinates z))
        \<in> borel_measurable lborel"
    by (rule measurable_compose[OF right_coordinates_measurable
          right_branch_output_borel_measurable])
  have root_measurable[measurable]:
      "((\<lambda>z :: slp_point \<times>
          ('i, 'j) slp_mixed_center_finite_coordinates. fst (snd z)))
        \<in> borel_measurable lborel"
    apply (simp only: measurable_lborel2)
    by (rule borel_measurable_continuous_onI) (intro continuous_intros)
  have quadratic_borel_measurable[measurable]:
      "slp_point_quadratic_value \<in> borel_measurable borel"
    unfolding slp_point_quadratic_value_def
    by (rule borel_measurable_continuous_onI) (intro continuous_intros)
  have core_measurable[measurable]:
      "(\<lambda>z :: slp_point \<times>
          ('i, 'j) slp_mixed_center_finite_coordinates.
        slp_mixed_core_residual (fst (snd z))
          (?left_branch_output (?left_coordinates z))
          (?right_branch_output (?right_coordinates z)))
        \<in> borel_measurable lborel"
    unfolding slp_mixed_core_residual_def
    by measurable
  have residual_measurable:
      "((\<lambda>z :: slp_point \<times>
          ('i, 'j) slp_mixed_center_finite_coordinates.
        slp_mixed_center_finite_residual (fst z) (snd z)))
        \<in> borel_measurable lborel"
  proof -
    have residual_eq:
        "((\<lambda>z :: slp_point \<times>
            ('i, 'j) slp_mixed_center_finite_coordinates.
          slp_mixed_center_finite_residual (fst z) (snd z))) =
        (\<lambda>z.
          ?left_branch_residual (?left_coordinates z) +
          ?right_branch_residual (?right_coordinates z) +
          slp_mixed_core_residual (fst (snd z))
            (?left_branch_output (?left_coordinates z))
            (?right_branch_output (?right_coordinates z)))"
      apply (rule ext)
      unfolding slp_mixed_center_finite_residual_def
        slp_mixed_branch_residual_def
        slp_right_branch_residual_def slp_left_branch_residual_def
        slp_mixed_center_finite_inserted_coordinates_def
      by (simp only: slp_left_branch_output_eq_right prod.sel)
    have branch_residuals_measurable:
        "(\<lambda>z.
          ?left_branch_residual (?left_coordinates z) +
          ?right_branch_residual (?right_coordinates z))
          \<in> borel_measurable lborel"
      by (rule borel_measurable_add[OF left_residual_measurable
            right_residual_measurable])
    have total_residual_measurable:
        "(\<lambda>z.
          (?left_branch_residual (?left_coordinates z) +
            ?right_branch_residual (?right_coordinates z)) +
          slp_mixed_core_residual (fst (snd z))
            (?left_branch_output (?left_coordinates z))
            (?right_branch_output (?right_coordinates z)))
          \<in> borel_measurable lborel"
      by (rule borel_measurable_add[OF branch_residuals_measurable
            core_measurable])
    show ?thesis
      using total_residual_measurable residual_eq by simp
  qed
  show ?thesis
    using residual_measurable by (simp only: lborel_prod split_beta')
qed

end
