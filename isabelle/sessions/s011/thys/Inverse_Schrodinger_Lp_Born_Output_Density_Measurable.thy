theory Inverse_Schrodinger_Lp_Born_Output_Density_Measurable
  imports Inverse_Schrodinger_Lp_Born_Output_Density
begin

section \<open>Measurability of positive Born output densities\<close>

theorem slp_positive_output_density_joint_measurable:
  assumes cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and potential_measurable[measurable]:
      "potential \<in> borel_measurable lborel"
    and terminal_weight_measurable[measurable]:
      "terminal_weight \<in> borel_measurable lborel"
  shows "case_prod
      (slp_positive_output_density R cutoff potential terminal_weight n)
    \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
proof (induction n)
  case 0
  note [measurable] = slp_localized_cauchy_kernel_borel_measurable
  show ?case
    by (simp only: slp_positive_output_density.simps; measurable)
next
  case (Suc n)
  note [measurable] = Suc.IH
    slp_localized_cauchy_kernel_borel_measurable
  show ?case
    by (simp only: slp_positive_output_density.simps; measurable)
qed

corollary slp_left_positive_output_density_joint_measurable:
  assumes cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_measurable: "potential \<in> borel_measurable lborel"
    and terminal_weight_measurable:
      "terminal_weight \<in> borel_measurable lborel"
  shows "case_prod
      (slp_left_positive_output_density R cutoff potential terminal_weight n)
    \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
  unfolding slp_left_positive_output_density_def
  by (rule slp_positive_output_density_joint_measurable[OF
        cutoff_measurable potential_measurable terminal_weight_measurable])

corollary slp_right_positive_output_density_joint_measurable:
  assumes cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_measurable: "potential \<in> borel_measurable lborel"
    and terminal_weight_measurable:
      "terminal_weight \<in> borel_measurable lborel"
  shows "case_prod
      (slp_right_positive_output_density R cutoff potential terminal_weight n)
    \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
  unfolding slp_right_positive_output_density_def
  by (rule slp_positive_output_density_joint_measurable[OF
        cutoff_measurable potential_measurable terminal_weight_measurable])

corollary slp_positive_output_density_output_measurable:
  assumes cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_measurable: "potential \<in> borel_measurable lborel"
    and terminal_weight_measurable:
      "terminal_weight \<in> borel_measurable lborel"
  shows "slp_positive_output_density R cutoff potential terminal_weight n origin
    \<in> borel_measurable lborel"
  using slp_positive_output_density_joint_measurable[OF cutoff_measurable
      potential_measurable terminal_weight_measurable]
  by measurable

end
