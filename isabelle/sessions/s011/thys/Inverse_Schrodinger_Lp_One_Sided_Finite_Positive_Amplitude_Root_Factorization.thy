theory Inverse_Schrodinger_Lp_One_Sided_Finite_Positive_Amplitude_Root_Factorization
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_One_Sided_Positive_Amplitude_Integral_Transport"
begin

section \<open>Root factorization of the finite positive amplitude\<close>

theorem slp_left_branch_positive_amplitude_finite_root_factorization:
  fixes branch_dummy :: "'i::finite itself"
  assumes root_weight_measurable:
      "root_weight \<in> borel_measurable lborel"
    and cutoff_measurable:
      "cutoff \<in> borel_measurable lborel"
    and potential_measurable:
      "potential \<in> borel_measurable lborel"
    and terminal_value_measurable:
      "terminal_value \<in> borel_measurable lborel"
    and output_factor_measurable:
      "output_factor \<in> borel_measurable lborel"
  shows
    "(\<integral>\<^sup>+ coordinates.
        slp_left_branch_positive_amplitude_finite R root_weight cutoff
          potential terminal_value output_factor coordinates
      \<partial>(lborel :: ('i slp_left_branch_finite_coordinates) measure)) =
      (\<integral>\<^sup>+ root. ennreal (norm (root_weight root)) *
        (\<integral>\<^sup>+ (branch_coordinates ::
            ((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point).
          slp_left_branch_positive_kernel_joint R cutoff potential
              terminal_value (root, branch_coordinates) *
            ennreal (norm (output_factor
              (slp_one_sided_packed_output_point
                (snd (slp_one_sided_finite_to_packed_coordinates
                  (root, branch_coordinates))))))
          \<partial>lborel) \<partial>lborel)"
proof -
  let ?amplitude =
    "(slp_left_branch_positive_amplitude_finite R root_weight cutoff
      potential terminal_value output_factor ::
        'i slp_left_branch_finite_coordinates \<Rightarrow> ennreal)"
  let ?branch_factor =
    "\<lambda>(root :: slp_point)
        (branch_coordinates ::
          ((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point).
      slp_left_branch_positive_kernel_joint R cutoff potential
          terminal_value (root, branch_coordinates) *
        ennreal (norm (output_factor
          (slp_one_sided_packed_output_point
            (snd (slp_one_sided_finite_to_packed_coordinates
              (root, branch_coordinates))))))"
  have amplitude_measurable:
      "?amplitude \<in> borel_measurable lborel"
    by (rule slp_left_branch_positive_amplitude_finite_measurable[OF
          root_weight_measurable cutoff_measurable potential_measurable
          terminal_value_measurable output_factor_measurable])
  have amplitude_product_measurable:
      "?amplitude \<in> borel_measurable
        ((lborel :: slp_point measure) \<Otimes>\<^sub>M
          (lborel :: (((slp_point^'i) \<times> (slp_point^'i)) \<times>
            slp_point) measure))"
    using amplitude_measurable by (simp only: lborel_prod)
  have branch_factor_measurable:
      "?branch_factor root \<in> borel_measurable lborel"
    for root
  proof -
    have pair_root_measurable:
        "(\<lambda>branch_coordinates ::
            ((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point.
          (root, branch_coordinates))
          \<in> measurable lborel lborel"
      apply (simp only: measurable_lborel1 measurable_lborel2)
      by (rule borel_measurable_continuous_onI) (intro continuous_intros)
    have kernel_measurable:
        "(slp_left_branch_positive_kernel_joint R cutoff potential
            terminal_value ::
          'i slp_left_branch_finite_coordinates \<Rightarrow> ennreal)
          \<in> borel_measurable lborel"
      by (rule slp_left_branch_positive_kernel_joint_measurable[OF
            cutoff_measurable potential_measurable
            terminal_value_measurable])
    have kernel_slice_measurable:
        "(\<lambda>branch_coordinates ::
            ((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point.
          slp_left_branch_positive_kernel_joint R cutoff potential
            terminal_value (root, branch_coordinates))
          \<in> borel_measurable lborel"
      using measurable_comp[OF pair_root_measurable kernel_measurable]
      by (simp only: comp_def)
    have finite_to_packed_measurable:
        "(slp_one_sided_finite_to_packed_coordinates ::
          'i slp_left_branch_finite_coordinates \<Rightarrow>
            (real^bool) \<times>
              (real^((unit + ('i + 'i)) \<times> bool)))
          \<in> measurable lborel (lborel \<Otimes>\<^sub>M lborel)"
      by (rule slp_one_sided_finite_to_packed_coordinates_measurable)
    have packed_slice_measurable:
        "(\<lambda>branch_coordinates ::
            ((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point.
          slp_one_sided_finite_to_packed_coordinates
            (root, branch_coordinates))
          \<in> measurable lborel (lborel \<Otimes>\<^sub>M lborel)"
      using measurable_comp[OF pair_root_measurable
        finite_to_packed_measurable]
      by (simp only: comp_def)
    have packed_branch_measurable:
        "(\<lambda>branch_coordinates ::
            ((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point.
          snd (slp_one_sided_finite_to_packed_coordinates
            (root, branch_coordinates)))
          \<in> measurable lborel lborel"
      using measurable_comp[OF packed_slice_measurable measurable_snd]
      by (simp only: comp_def)
    have output_point_measurable:
        "(\<lambda>branch_coordinates ::
            ((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point.
          slp_one_sided_packed_output_point
            (snd (slp_one_sided_finite_to_packed_coordinates
              (root, branch_coordinates))))
          \<in> borel_measurable lborel"
      using measurable_comp[OF packed_branch_measurable
        slp_one_sided_packed_output_point_measurable]
      by (simp only: comp_def)
    have output_point_lborel:
        "(\<lambda>branch_coordinates ::
            ((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point.
          slp_one_sided_packed_output_point
            (snd (slp_one_sided_finite_to_packed_coordinates
              (root, branch_coordinates))))
          \<in> measurable lborel lborel"
      using output_point_measurable
      by (simp only: measurable_lborel1)
    have output_value_measurable:
        "(\<lambda>branch_coordinates ::
            ((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point.
          output_factor (slp_one_sided_packed_output_point
            (snd (slp_one_sided_finite_to_packed_coordinates
              (root, branch_coordinates)))))
          \<in> borel_measurable lborel"
      using measurable_comp[OF output_point_lborel
        output_factor_measurable]
      by (simp only: comp_def)
    have output_norm_measurable:
        "(\<lambda>branch_coordinates ::
            ((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point.
          ennreal (norm (output_factor
            (slp_one_sided_packed_output_point
              (snd (slp_one_sided_finite_to_packed_coordinates
                (root, branch_coordinates)))))))
          \<in> borel_measurable lborel"
      using output_value_measurable by measurable
    have kernel_slice_borel:
        "(\<lambda>branch_coordinates ::
            ((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point.
          slp_left_branch_positive_kernel_joint R cutoff potential
            terminal_value (root, branch_coordinates))
          \<in> borel_measurable borel"
      using kernel_slice_measurable
      by (simp only: measurable_lborel2)
    have output_norm_borel:
        "(\<lambda>branch_coordinates ::
            ((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point.
          ennreal (norm (output_factor
            (slp_one_sided_packed_output_point
              (snd (slp_one_sided_finite_to_packed_coordinates
                (root, branch_coordinates)))))))
          \<in> borel_measurable borel"
      using output_norm_measurable
      by (simp only: measurable_lborel2)
    show ?thesis
      apply (simp only: measurable_lborel2)
      apply (rule borel_measurable_times_ennreal)
       apply (rule kernel_slice_borel)
      apply (rule output_norm_borel)
      done
  qed
  have inner_factorization:
      "(\<integral>\<^sup>+ branch_coordinates.
          ?amplitude (root, branch_coordinates) \<partial>lborel) =
        ennreal (norm (root_weight root)) *
          (\<integral>\<^sup>+ branch_coordinates.
            ?branch_factor root branch_coordinates \<partial>lborel)"
    for root
  proof -
    show ?thesis
      apply (simp only: slp_left_branch_positive_amplitude_finite_factors
          fst_conv mult.assoc)
      by (rule nn_integral_cmult[OF branch_factor_measurable])
  qed
  have split:
      "(\<integral>\<^sup>+ coordinates. ?amplitude coordinates
          \<partial>(lborel :: ('i slp_left_branch_finite_coordinates) measure)) =
        (\<integral>\<^sup>+ root. \<integral>\<^sup>+ branch_coordinates.
          ?amplitude (root, branch_coordinates) \<partial>lborel \<partial>lborel)"
  proof -
    note fubini =
      lborel.nn_integral_fst[OF amplitude_product_measurable]
    show ?thesis
      using fubini by (simp only: lborel_prod)
  qed
  show ?thesis
    apply (rule trans[OF split])
    apply (rule nn_integral_cong)
    apply (simp only: slp_left_branch_positive_amplitude_finite_factors
        fst_conv mult.assoc)
    apply (subst nn_integral_cmult)
    apply (rule branch_factor_measurable)
    by (simp only: mult.assoc)
qed

end
