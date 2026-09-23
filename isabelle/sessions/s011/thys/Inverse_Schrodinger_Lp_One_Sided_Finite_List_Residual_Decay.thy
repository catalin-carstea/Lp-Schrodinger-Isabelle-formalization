theory Inverse_Schrodinger_Lp_One_Sided_Finite_List_Residual_Decay
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_One_Sided_Finite_Residual_Identity"
begin

section \<open>One-sided decay in the manuscript's finite-list coordinates\<close>

theorem slp_left_branch_complex_amplitude_finite_list_residual_decay:
  fixes branch_dummy :: "'i::finite itself"
  assumes stationary_phase:
      "hormander_quadratic_stationary_phase_decay_claim
        TYPE(('i + 'i) \<times> bool)"
    and density:
      "evans_compact_smooth_l1_density_claim TYPE(('i + 'i) \<times> bool)"
    and B_nonnegative: "0 \<le> B"
    and root_support: "\<And>x. root_weight x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and cutoff_support: "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and potential_support: "\<And>x. potential x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and root_weight_measurable:
      "root_weight \<in> borel_measurable lborel"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_measurable: "potential \<in> borel_measurable lborel"
    and terminal_value_measurable:
      "terminal_value \<in> borel_measurable lborel"
    and output_factor_measurable:
      "output_factor \<in> borel_measurable lborel"
    and majorant_finite:
      "(\<integral>\<^sup>+ coordinates.
        case_prod (slp_left_branch_positive_amplitude_packed (2 * B)
          root_weight cutoff potential terminal_value output_factor)
          coordinates \<partial>((lborel :: (real^bool) measure) \<Otimes>\<^sub>M
            (lborel :: (real^((unit + ('i + 'i)) \<times> bool)) measure))) <
        \<infinity>"
  shows
    "((\<lambda>omega. integral\<^sup>L lborel
      (\<lambda>(coordinates :: 'i slp_left_branch_finite_coordinates).
        exp (\<i> * of_real
          (omega * slp_left_branch_residual
            (slp_finite_branch_pair_list
              (\<lambda>i. fst (fst (snd coordinates)) $ i)
              (\<lambda>i. snd (fst (snd coordinates)) $ i))
            (snd (snd coordinates)))) *
        slp_left_branch_complex_amplitude_finite root_weight cutoff potential
          terminal_value output_factor coordinates))
      \<longlongrightarrow> 0) at_top"
  apply (subst slp_one_sided_finite_residual_eq_left_branch[symmetric])
  by (rule slp_left_branch_complex_amplitude_finite_residual_decay[
        OF stationary_phase density B_nonnegative root_support cutoff_support
          potential_support root_weight_measurable cutoff_measurable
          potential_measurable terminal_value_measurable
          output_factor_measurable majorant_finite])

end
