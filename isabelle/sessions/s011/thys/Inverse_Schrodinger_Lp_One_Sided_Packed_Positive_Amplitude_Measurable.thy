theory Inverse_Schrodinger_Lp_One_Sided_Packed_Positive_Amplitude_Measurable
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_One_Sided_Finite_Positive_Amplitude_Measurable"
begin

section \<open>Measurability of the packed positive amplitude\<close>

theorem slp_left_branch_positive_amplitude_packed_measurable:
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
    "(case_prod (slp_left_branch_positive_amplitude_packed R root_weight
        cutoff potential terminal_value output_factor) ::
      (real^bool) \<times>
        (real^((unit + ('i + 'i)) \<times> bool)) \<Rightarrow> ennreal)
      \<in> borel_measurable lborel"
proof -
  have finite_measurable:
      "(slp_left_branch_positive_amplitude_finite R root_weight cutoff
          potential terminal_value output_factor ::
        'i slp_left_branch_finite_coordinates \<Rightarrow> ennreal)
        \<in> borel_measurable lborel"
    by (rule slp_left_branch_positive_amplitude_finite_measurable[OF
          root_weight_measurable cutoff_measurable potential_measurable
          terminal_value_measurable output_factor_measurable])
  have composed_product:
      "(\<lambda>coordinates :: (real^bool) \<times>
          (real^((unit + ('i + 'i)) \<times> bool)).
        slp_left_branch_positive_amplitude_finite R root_weight cutoff
          potential terminal_value output_factor
          (slp_one_sided_packed_to_finite_coordinates coordinates))
        \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    using measurable_comp[OF
      slp_one_sided_packed_to_finite_coordinates_measurable
      finite_measurable]
    by (simp only: comp_def)
  have composed:
      "(\<lambda>coordinates :: (real^bool) \<times>
          (real^((unit + ('i + 'i)) \<times> bool)).
        slp_left_branch_positive_amplitude_finite R root_weight cutoff
          potential terminal_value output_factor
          (slp_one_sided_packed_to_finite_coordinates coordinates))
        \<in> borel_measurable lborel"
    using composed_product by (simp only: lborel_prod)
  have identity:
      "(case_prod (slp_left_branch_positive_amplitude_packed R root_weight
          cutoff potential terminal_value output_factor) ::
        (real^bool) \<times>
          (real^((unit + ('i + 'i)) \<times> bool)) \<Rightarrow> ennreal) =
        (\<lambda>coordinates.
          slp_left_branch_positive_amplitude_finite R root_weight cutoff
            potential terminal_value output_factor
            (slp_one_sided_packed_to_finite_coordinates coordinates))"
  proof (rule ext)
    fix coordinates :: "(real^bool) \<times>
      (real^((unit + ('i + 'i)) \<times> bool))"
    obtain root branch where coordinates: "coordinates = (root, branch)"
      by (cases coordinates)
    show "case_prod (slp_left_branch_positive_amplitude_packed R root_weight
          cutoff potential terminal_value output_factor) coordinates =
        slp_left_branch_positive_amplitude_finite R root_weight cutoff
          potential terminal_value output_factor
          (slp_one_sided_packed_to_finite_coordinates coordinates)"
      unfolding coordinates slp_left_branch_positive_amplitude_finite_def
      by (simp only: slp_one_sided_packed_to_finite_to_packed split_beta)
  qed
  show ?thesis
    using composed unfolding identity .
qed

end
