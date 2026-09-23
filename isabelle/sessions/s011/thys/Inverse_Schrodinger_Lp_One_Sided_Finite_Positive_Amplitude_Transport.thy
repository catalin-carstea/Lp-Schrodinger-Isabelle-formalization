theory Inverse_Schrodinger_Lp_One_Sided_Finite_Positive_Amplitude_Transport
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_One_Sided_Finite_NN_Integral_Transport"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_Left_Complex_Amplitude_Packed"
begin

section \<open>Finite pullback of the exact positive amplitude\<close>

definition slp_left_branch_positive_amplitude_finite ::
    "real \<Rightarrow> (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      'i::finite slp_left_branch_finite_coordinates \<Rightarrow> ennreal"
where
  "slp_left_branch_positive_amplitude_finite R root_weight cutoff potential
      terminal_value output_factor coordinates =
    case_prod (slp_left_branch_positive_amplitude_packed R root_weight cutoff
      potential terminal_value output_factor)
      (slp_one_sided_finite_to_packed_coordinates coordinates)"

theorem slp_left_branch_positive_amplitude_finite_integral:
  fixes branch_dummy :: "'i::finite itself"
  assumes amplitude_measurable:
    "(case_prod (slp_left_branch_positive_amplitude_packed R root_weight cutoff
        potential terminal_value output_factor) ::
      (real^bool) \<times>
        (real^((unit + ('i + 'i)) \<times> bool)) \<Rightarrow> ennreal)
      \<in> borel_measurable lborel"
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
  from slp_one_sided_finite_packed_nn_integral[
      where 'i = 'i and F =
        "case_prod (slp_left_branch_positive_amplitude_packed R root_weight
          cutoff potential terminal_value output_factor)",
      OF amplitude_measurable]
  show ?thesis
    by (simp only: lborel_prod
        slp_left_branch_positive_amplitude_finite_def)
qed

end
