theory Inverse_Schrodinger_Lp_One_Sided_Finite_Positive_Inner_Mass
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_One_Sided_Positive_Amplitude_Finite_Bound"
begin

section \<open>Named finite-coordinate positive inner mass\<close>

definition slp_left_branch_positive_inner_mass_finite ::
    "'i::finite itself \<Rightarrow> real \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow> slp_point \<Rightarrow> ennreal"
where
  "slp_left_branch_positive_inner_mass_finite dimension_type R cutoff
      potential terminal_value output_factor origin =
    (\<integral>\<^sup>+ (branch_coordinates ::
        ((slp_point^'i) \<times> (slp_point^'i)) \<times> slp_point).
      slp_left_branch_positive_kernel_joint R cutoff potential terminal_value
          (origin, branch_coordinates) *
        ennreal (norm (output_factor
          (slp_one_sided_packed_output_point
            (snd (slp_one_sided_finite_to_packed_coordinates
              (origin, branch_coordinates))))))
      \<partial>lborel)"

theorem slp_left_branch_positive_amplitude_packed_lt_top_from_inner_mass:
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
    and inner_mass_uniform:
      "\<exists>M. M < top \<and>
        (\<forall>root. slp_left_branch_positive_inner_mass_finite TYPE('i) R
          cutoff potential terminal_value output_factor root \<le> M)"
  shows
    "(\<integral>\<^sup>+ coordinates.
        case_prod (slp_left_branch_positive_amplitude_packed R root_weight
          cutoff potential terminal_value output_factor) coordinates
      \<partial>((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
        (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure))) < top"
proof -
  obtain M where M_finite: "M < top"
    and inner_bound:
      "\<And>root. slp_left_branch_positive_inner_mass_finite TYPE('i) R
        cutoff potential terminal_value output_factor root \<le> M"
    using inner_mass_uniform by blast
  show ?thesis
    by (rule slp_left_branch_positive_amplitude_packed_lt_top[
          where B = M, OF root_weight_integrable cutoff_measurable
            potential_measurable terminal_value_measurable
            output_factor_measurable _ M_finite])
      (use inner_bound in
        \<open>simp only: slp_left_branch_positive_inner_mass_finite_def\<close>)
qed

end
