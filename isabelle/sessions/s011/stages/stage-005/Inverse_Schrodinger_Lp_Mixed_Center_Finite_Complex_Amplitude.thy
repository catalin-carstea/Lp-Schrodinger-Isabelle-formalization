theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Complex_Amplitude
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_005.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Residual"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_004.Inverse_Schrodinger_Lp_Right_Graph_Finite_Modulation"
begin

section \<open>Exact finite mixed amplitude on the solved center fiber\<close>

theorem slp_mixed_center_finite_inserted_coordinates_measurable:
  "((\<lambda>z :: slp_point \<times>
      ('i::finite, 'j::finite) slp_mixed_center_finite_coordinates.
      slp_mixed_center_finite_inserted_coordinates (fst z) (snd z)))
    \<in> borel_measurable lborel"
proof -
  let ?left_coordinates =
    "\<lambda>z :: slp_point \<times>
        ('i, 'j) slp_mixed_center_finite_coordinates.
      (fst (snd z), fst (snd (snd z)))"
  let ?right_zero_coordinates =
    "\<lambda>z :: slp_point \<times>
        ('i, 'j) slp_mixed_center_finite_coordinates.
      (fst (snd z), (snd (snd (snd z)), 0))"
  let ?finite_output =
    "\<lambda>(coordinates :: 'i slp_left_branch_finite_coordinates).
      slp_left_branch_output
        (slp_finite_branch_pair_list
          (\<lambda>i. fst (fst (snd coordinates)) $ i)
          (\<lambda>i. snd (fst (snd coordinates)) $ i))
        (snd (snd coordinates))"
  let ?right_finite_output =
    "\<lambda>(coordinates :: 'j slp_left_branch_finite_coordinates).
      slp_left_branch_output
        (slp_finite_branch_pair_list
          (\<lambda>i. fst (fst (snd coordinates)) $ i)
          (\<lambda>i. snd (fst (snd coordinates)) $ i))
        (snd (snd coordinates))"
  have left_coordinates_measurable:
      "?left_coordinates \<in> borel_measurable lborel"
    apply (simp only: measurable_lborel2)
    by (rule borel_measurable_continuous_onI) (intro continuous_intros)
  have right_zero_coordinates_measurable:
      "?right_zero_coordinates \<in> borel_measurable lborel"
    apply (simp only: measurable_lborel2)
    by (rule borel_measurable_continuous_onI) (intro continuous_intros)
  have finite_output_measurable:
      "?finite_output \<in> borel_measurable lborel"
    by (rule slp_left_branch_finite_output_measurable)
  have right_finite_output_measurable:
      "?right_finite_output \<in> borel_measurable lborel"
    by (rule slp_left_branch_finite_output_measurable)
  have finite_output_borel_measurable:
      "?finite_output \<in> borel_measurable borel"
    using finite_output_measurable by (simp only: measurable_lborel2)
  have right_finite_output_borel_measurable:
      "?right_finite_output \<in> borel_measurable borel"
    using right_finite_output_measurable by (simp only: measurable_lborel2)
  have left_output_measurable[measurable]:
      "(\<lambda>z. ?finite_output (?left_coordinates z))
        \<in> borel_measurable lborel"
    by (rule measurable_compose[OF left_coordinates_measurable
          finite_output_borel_measurable])
  have right_output_measurable[measurable]:
      "(\<lambda>z. ?right_finite_output (?right_zero_coordinates z))
        \<in> borel_measurable lborel"
    by (rule measurable_compose[OF right_zero_coordinates_measurable
          right_finite_output_borel_measurable])
  have left_output_borel_measurable[measurable]:
      "(\<lambda>z. ?finite_output (?left_coordinates z))
        \<in> borel_measurable borel"
    using left_output_measurable by (simp only: measurable_lborel2)
  have right_output_borel_measurable[measurable]:
      "(\<lambda>z. ?right_finite_output (?right_zero_coordinates z))
        \<in> borel_measurable borel"
    using right_output_measurable by (simp only: measurable_lborel2)
  have terminal_measurable[measurable]:
      "((\<lambda>z :: slp_point \<times>
          ('i, 'j) slp_mixed_center_finite_coordinates.
        slp_mixed_center_finite_right_terminal (fst z) (snd z)))
        \<in> borel_measurable lborel"
  proof -
    have center_borel_measurable[measurable]:
        "((\<lambda>z :: slp_point \<times>
            ('i, 'j) slp_mixed_center_finite_coordinates. fst z))
          \<in> borel_measurable borel"
      by (rule borel_measurable_continuous_onI) (intro continuous_intros)
    have root_borel_measurable[measurable]:
        "((\<lambda>z :: slp_point \<times>
            ('i, 'j) slp_mixed_center_finite_coordinates. fst (snd z)))
          \<in> borel_measurable borel"
      by (rule borel_measurable_continuous_onI) (intro continuous_intros)
    have center_plus_root_borel_measurable:
        "((\<lambda>z :: slp_point \<times>
            ('i, 'j) slp_mixed_center_finite_coordinates.
          fst z + fst (snd z))) \<in> borel_measurable borel"
      by (rule borel_measurable_add[
            OF center_borel_measurable root_borel_measurable])
    have left_subtracted_borel_measurable:
        "((\<lambda>z :: slp_point \<times>
            ('i, 'j) slp_mixed_center_finite_coordinates.
          fst z + fst (snd z) - ?finite_output (?left_coordinates z)))
          \<in> borel_measurable borel"
      by (rule borel_measurable_diff[
            OF center_plus_root_borel_measurable
              left_output_borel_measurable])
    have terminal_expression_borel_measurable:
        "((\<lambda>z :: slp_point \<times>
            ('i, 'j) slp_mixed_center_finite_coordinates.
          fst z + fst (snd z) - ?finite_output (?left_coordinates z) -
            ?right_finite_output (?right_zero_coordinates z)))
          \<in> borel_measurable borel"
      by (rule borel_measurable_diff[
            OF left_subtracted_borel_measurable
              right_output_borel_measurable])
    have terminal_borel_measurable:
        "((\<lambda>z :: slp_point \<times>
            ('i, 'j) slp_mixed_center_finite_coordinates.
          slp_mixed_center_finite_right_terminal (fst z) (snd z)))
          \<in> borel_measurable borel"
      using terminal_expression_borel_measurable
      unfolding slp_mixed_center_finite_right_terminal_def
      by (simp only: slp_left_branch_output_eq_right prod.sel)
    show ?thesis
      using terminal_borel_measurable by (simp only: measurable_lborel2)
  qed
  have root_coordinates_measurable:
      "((\<lambda>z :: slp_point \<times>
          ('i, 'j) slp_mixed_center_finite_coordinates. fst (snd z)))
        \<in> borel_measurable lborel"
    apply (simp only: measurable_lborel2)
    by (rule borel_measurable_continuous_onI) (intro continuous_intros)
  have right_family_measurable:
      "((\<lambda>z :: slp_point \<times>
          ('i, 'j) slp_mixed_center_finite_coordinates.
        snd (snd (snd z)))) \<in> borel_measurable lborel"
    apply (simp only: measurable_lborel2)
    by (rule borel_measurable_continuous_onI) (intro continuous_intros)
  have right_family_terminal_measurable:
      "((\<lambda>z :: slp_point \<times>
          ('i, 'j) slp_mixed_center_finite_coordinates.
        (snd (snd (snd z)),
          slp_mixed_center_finite_right_terminal (fst z) (snd z))))
        \<in> borel_measurable lborel"
    by (rule borel_measurable_Pair[
          OF right_family_measurable terminal_measurable])
  have right_coordinates_measurable:
      "((\<lambda>z :: slp_point \<times>
          ('i, 'j) slp_mixed_center_finite_coordinates.
        (fst (snd z),
          (snd (snd (snd z)),
            slp_mixed_center_finite_right_terminal (fst z) (snd z)))))
        \<in> borel_measurable lborel"
    by (rule borel_measurable_Pair[
          OF root_coordinates_measurable right_family_terminal_measurable])
  have inserted_pair_measurable:
      "((\<lambda>z :: slp_point \<times>
          ('i, 'j) slp_mixed_center_finite_coordinates.
        (?left_coordinates z,
          (fst (snd z),
            (snd (snd (snd z)),
              slp_mixed_center_finite_right_terminal (fst z) (snd z))))))
        \<in> borel_measurable lborel"
    by (rule borel_measurable_Pair[
          OF left_coordinates_measurable right_coordinates_measurable])
  show ?thesis
    unfolding slp_mixed_center_finite_inserted_coordinates_def
    using inserted_pair_measurable by (simp only: prod.sel)
qed

definition slp_mixed_center_finite_complex_amplitude ::
    "(slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      slp_point \<Rightarrow>
      ('i::finite, 'j::finite) slp_mixed_center_finite_coordinates \<Rightarrow>
      complex"
where
  "slp_mixed_center_finite_complex_amplitude root_weight left_cutoff
      left_potential right_cutoff right_potential center coordinates =
    root_weight (fst coordinates) *
      slp_left_branch_complex_kernel_joint left_cutoff left_potential
        (\<lambda>_. 1)
        (fst (slp_mixed_center_finite_inserted_coordinates center coordinates)) *
      slp_right_branch_complex_kernel_joint right_cutoff right_potential
        (\<lambda>_. 1)
        (snd (slp_mixed_center_finite_inserted_coordinates center coordinates))"

theorem slp_mixed_center_finite_complex_amplitude_measurable:
  assumes root_weight_measurable[measurable]:
      "root_weight \<in> borel_measurable lborel"
    and left_cutoff_measurable[measurable]:
      "left_cutoff \<in> borel_measurable lborel"
    and left_potential_measurable[measurable]:
      "left_potential \<in> borel_measurable lborel"
    and right_cutoff_measurable[measurable]:
      "right_cutoff \<in> borel_measurable lborel"
    and right_potential_measurable[measurable]:
      "right_potential \<in> borel_measurable lborel"
  shows
    "((\<lambda>z :: slp_point \<times>
        ('i::finite, 'j::finite) slp_mixed_center_finite_coordinates.
      slp_mixed_center_finite_complex_amplitude root_weight left_cutoff
        left_potential right_cutoff right_potential (fst z) (snd z)))
      \<in> borel_measurable lborel"
proof -
  have inserted_measurable:
      "((\<lambda>z :: slp_point \<times>
          ('i, 'j) slp_mixed_center_finite_coordinates.
        slp_mixed_center_finite_inserted_coordinates (fst z) (snd z)))
        \<in> borel_measurable lborel"
    by (rule slp_mixed_center_finite_inserted_coordinates_measurable)
  have inserted_product_measurable:
      "((\<lambda>z :: slp_point \<times>
          ('i, 'j) slp_mixed_center_finite_coordinates.
        slp_mixed_center_finite_inserted_coordinates (fst z) (snd z)))
        \<in> measurable lborel (lborel \<Otimes>\<^sub>M lborel)"
    using inserted_measurable
    by (simp only: lborel_prod measurable_lborel1)
  have left_coordinates_measurable[measurable]:
      "((\<lambda>z. fst (slp_mixed_center_finite_inserted_coordinates
          (fst z) (snd z))) ::
          (slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates)
            \<Rightarrow> 'i slp_left_branch_finite_coordinates)
        \<in> borel_measurable lborel"
    using measurable_compose[OF inserted_product_measurable measurable_fst]
    by (simp add: comp_def measurable_lborel1)
  have right_coordinates_measurable[measurable]:
      "((\<lambda>z. snd (slp_mixed_center_finite_inserted_coordinates
          (fst z) (snd z))) ::
          (slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates)
            \<Rightarrow> 'j slp_left_branch_finite_coordinates)
        \<in> borel_measurable lborel"
    using measurable_compose[OF inserted_product_measurable measurable_snd]
    by (simp add: comp_def measurable_lborel1)
  have left_kernel_measurable:
      "(slp_left_branch_complex_kernel_joint left_cutoff left_potential
          (\<lambda>_. 1) ::
        'i slp_left_branch_finite_coordinates \<Rightarrow> complex)
        \<in> borel_measurable lborel"
  proof -
    have unit_measurable:
        "(\<lambda>_ :: slp_point. (1 :: complex))
          \<in> borel_measurable lborel"
      by measurable
    show ?thesis
      by (rule slp_left_branch_complex_kernel_joint_measurable[
            OF left_cutoff_measurable left_potential_measurable
              unit_measurable])
  qed
  have cnj_borel_measurable: "cnj \<in> borel_measurable borel"
    by (rule borel_measurable_continuous_onI) (intro continuous_intros)
  have conjugate_cutoff_measurable[measurable]:
      "(\<lambda>x. cnj (right_cutoff x)) \<in> borel_measurable lborel"
    using measurable_comp[OF right_cutoff_measurable cnj_borel_measurable]
    by (simp add: comp_def)
  have conjugate_potential_measurable[measurable]:
      "(\<lambda>x. cnj (right_potential x)) \<in> borel_measurable lborel"
    using measurable_comp[OF right_potential_measurable cnj_borel_measurable]
    by (simp add: comp_def)
  have conjugate_terminal_measurable[measurable]:
      "(\<lambda>x :: slp_point. cnj (1 :: complex))
        \<in> borel_measurable lborel"
    by measurable
  have right_inner_measurable:
      "(slp_left_branch_complex_kernel_joint
          (\<lambda>x. cnj (right_cutoff x))
          (\<lambda>x. cnj (right_potential x))
          (\<lambda>x. cnj (1 :: complex)) ::
        'j slp_left_branch_finite_coordinates \<Rightarrow> complex)
        \<in> borel_measurable lborel"
    by (rule slp_left_branch_complex_kernel_joint_measurable[
          OF conjugate_cutoff_measurable conjugate_potential_measurable
            conjugate_terminal_measurable])
  have right_kernel_measurable:
      "(slp_right_branch_complex_kernel_joint right_cutoff right_potential
          (\<lambda>_. 1) ::
        'j slp_left_branch_finite_coordinates \<Rightarrow> complex)
        \<in> borel_measurable lborel"
    unfolding slp_right_branch_complex_kernel_joint_def
    using measurable_comp[OF right_inner_measurable cnj_borel_measurable]
    by (simp add: comp_def)
  have left_kernel_borel_measurable:
      "(slp_left_branch_complex_kernel_joint left_cutoff left_potential
          (\<lambda>_. 1) ::
        'i slp_left_branch_finite_coordinates \<Rightarrow> complex)
        \<in> borel_measurable borel"
    using left_kernel_measurable by (simp only: measurable_lborel2)
  have right_kernel_borel_measurable:
      "(slp_right_branch_complex_kernel_joint right_cutoff right_potential
          (\<lambda>_. 1) ::
        'j slp_left_branch_finite_coordinates \<Rightarrow> complex)
        \<in> borel_measurable borel"
    using right_kernel_measurable by (simp only: measurable_lborel2)
  have left_kernel_composed[measurable]:
      "((\<lambda>z. slp_left_branch_complex_kernel_joint left_cutoff
          left_potential (\<lambda>_. 1)
          (fst (slp_mixed_center_finite_inserted_coordinates
            (fst z) (snd z)))) ::
          (slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates)
            \<Rightarrow> complex)
        \<in> borel_measurable lborel"
    using measurable_compose[OF left_coordinates_measurable
        left_kernel_borel_measurable]
    unfolding comp_def .
  have right_kernel_composed[measurable]:
      "((\<lambda>z. slp_right_branch_complex_kernel_joint right_cutoff
          right_potential (\<lambda>_. 1)
          (snd (slp_mixed_center_finite_inserted_coordinates
            (fst z) (snd z)))) ::
          (slp_point \<times> ('i, 'j) slp_mixed_center_finite_coordinates)
            \<Rightarrow> complex)
        \<in> borel_measurable lborel"
    using measurable_compose[OF right_coordinates_measurable
        right_kernel_borel_measurable]
    unfolding comp_def .
  have root_coordinates_measurable:
      "((\<lambda>z :: slp_point \<times>
          ('i, 'j) slp_mixed_center_finite_coordinates. fst (snd z)))
        \<in> borel_measurable lborel"
    apply (simp only: measurable_lborel2)
    by (rule borel_measurable_continuous_onI) (intro continuous_intros)
  have root_weight_borel_measurable:
      "root_weight \<in> borel_measurable borel"
    using root_weight_measurable by (simp only: measurable_lborel2)
  have root_weight_composed:
      "((\<lambda>z :: slp_point \<times>
          ('i, 'j) slp_mixed_center_finite_coordinates.
        root_weight (fst (snd z)))) \<in> borel_measurable lborel"
    by (rule measurable_compose[
          OF root_coordinates_measurable root_weight_borel_measurable])
  have root_left_product_measurable:
      "((\<lambda>z :: slp_point \<times>
          ('i, 'j) slp_mixed_center_finite_coordinates.
        root_weight (fst (snd z)) *
          slp_left_branch_complex_kernel_joint left_cutoff left_potential
            (\<lambda>_. 1)
            (fst (slp_mixed_center_finite_inserted_coordinates
              (fst z) (snd z))))) \<in> borel_measurable lborel"
    by (rule borel_measurable_times[
          OF root_weight_composed left_kernel_composed])
  show ?thesis
    unfolding slp_mixed_center_finite_complex_amplitude_def
    by (rule borel_measurable_times[
          OF root_left_product_measurable right_kernel_composed])
qed

end
