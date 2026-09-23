theory Inverse_Schrodinger_Lp_One_Sided_Positive_Amplitude_Integral_Transport
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_One_Sided_Packed_Positive_Amplitude_Measurable"
begin

section \<open>Exact positive-amplitude integral transport\<close>

theorem slp_left_branch_positive_amplitude_integral_transport:
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
        case_prod (slp_left_branch_positive_amplitude_packed R root_weight
          cutoff potential terminal_value output_factor) coordinates
      \<partial>((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
        (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure))) =
      (\<integral>\<^sup>+ coordinates.
        slp_left_branch_positive_amplitude_finite R root_weight cutoff
          potential terminal_value output_factor coordinates
      \<partial>(lborel :: ('i slp_left_branch_finite_coordinates) measure))"
proof -
  have amplitude_measurable:
      "(case_prod (slp_left_branch_positive_amplitude_packed R root_weight
          cutoff potential terminal_value output_factor) ::
        (real^bool) \<times>
          (real^((unit + ('i + 'i)) \<times> bool)) \<Rightarrow> ennreal)
        \<in> borel_measurable lborel"
    by (rule slp_left_branch_positive_amplitude_packed_measurable[OF
          root_weight_measurable cutoff_measurable potential_measurable
          terminal_value_measurable output_factor_measurable])
  show ?thesis
    by (rule slp_left_branch_positive_amplitude_finite_integral[OF
          amplitude_measurable])
qed

end
