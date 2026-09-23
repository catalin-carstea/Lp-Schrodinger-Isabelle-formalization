theory Inverse_Schrodinger_Lp_One_Sided_Positive_Amplitude_Finite_Bound
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_One_Sided_Finite_Positive_Amplitude_Root_Factorization"
begin

section \<open>Conditional finiteness of the packed positive amplitude\<close>

theorem slp_left_branch_positive_amplitude_packed_lt_top:
  fixes branch_dummy :: "'i::finite itself"
  assumes root_weight_integrable:
      "integrable lborel root_weight"
    and cutoff_measurable:
      "cutoff \<in> borel_measurable lborel"
    and potential_measurable:
      "potential \<in> borel_measurable lborel"
    and terminal_value_measurable:
      "terminal_value \<in> borel_measurable lborel"
    and output_factor_measurable:
      "output_factor \<in> borel_measurable lborel"
    and inner_bound:
      "\<And>root. (\<integral>\<^sup>+ (branch_coordinates ::
          ((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point).
        slp_left_branch_positive_kernel_joint R cutoff potential
            terminal_value (root, branch_coordinates) *
          ennreal (norm (output_factor
            (slp_one_sided_packed_output_point
              (snd (slp_one_sided_finite_to_packed_coordinates
                (root, branch_coordinates))))))
        \<partial>lborel) \<le> B"
    and B_finite: "B < top"
  shows
    "(\<integral>\<^sup>+ coordinates.
        case_prod (slp_left_branch_positive_amplitude_packed R root_weight
          cutoff potential terminal_value output_factor) coordinates
      \<partial>((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
        (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure))) < top"
proof -
  have root_weight_measurable:
      "root_weight \<in> borel_measurable lborel"
    using root_weight_integrable
    unfolding integrable_iff_bounded by blast
  have root_norm_measurable:
      "(\<lambda>root. ennreal (norm (root_weight root)))
        \<in> borel_measurable lborel"
    using root_weight_measurable by measurable
  have root_norm_finite:
      "(\<integral>\<^sup>+ root. ennreal (norm (root_weight root))
        \<partial>lborel) < top"
    using root_weight_integrable
    unfolding integrable_iff_bounded by simp
  have transport:
      "(\<integral>\<^sup>+ coordinates.
          case_prod (slp_left_branch_positive_amplitude_packed R root_weight
            cutoff potential terminal_value output_factor) coordinates
        \<partial>((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
          (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure))) =
        (\<integral>\<^sup>+ coordinates.
          slp_left_branch_positive_amplitude_finite R root_weight cutoff
            potential terminal_value output_factor coordinates
        \<partial>(lborel :: ('i slp_left_branch_finite_coordinates) measure))"
    by (rule slp_left_branch_positive_amplitude_integral_transport[OF
          root_weight_measurable cutoff_measurable potential_measurable
          terminal_value_measurable output_factor_measurable])
  have factorization:
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
    by (rule slp_left_branch_positive_amplitude_finite_root_factorization[OF
          root_weight_measurable cutoff_measurable potential_measurable
          terminal_value_measurable output_factor_measurable])
  have outer_bound:
      "(\<integral>\<^sup>+ root. ennreal (norm (root_weight root)) *
          (\<integral>\<^sup>+ (branch_coordinates ::
              ((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point).
            slp_left_branch_positive_kernel_joint R cutoff potential
                terminal_value (root, branch_coordinates) *
              ennreal (norm (output_factor
                (slp_one_sided_packed_output_point
                  (snd (slp_one_sided_finite_to_packed_coordinates
                    (root, branch_coordinates))))))
            \<partial>lborel) \<partial>lborel) \<le>
        (\<integral>\<^sup>+ root. ennreal (norm (root_weight root)) * B
          \<partial>lborel)"
    by (rule nn_integral_mono)
       (rule mult_left_mono[OF inner_bound], simp)
  have factor:
      "(\<integral>\<^sup>+ root. ennreal (norm (root_weight root)) * B
          \<partial>lborel) =
        (\<integral>\<^sup>+ root. ennreal (norm (root_weight root))
          \<partial>lborel) * B"
    by (rule nn_integral_multc[OF root_norm_measurable])
  have bound_finite:
      "(\<integral>\<^sup>+ root. ennreal (norm (root_weight root))
          \<partial>lborel) * B < top"
    using root_norm_finite B_finite
    by (simp add: ennreal_mult_less_top)
  show ?thesis
    apply (subst transport)
    apply (subst factorization)
    apply (rule le_less_trans[OF outer_bound])
    apply (subst factor)
    by (rule bound_finite)
qed

end
