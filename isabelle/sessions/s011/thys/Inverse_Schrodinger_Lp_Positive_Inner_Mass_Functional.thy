theory Inverse_Schrodinger_Lp_Positive_Inner_Mass_Functional
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Natural_Positive_Inner_Mass_List"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Positive_Kernel_List_Functional_Induction"
begin

section \<open>The finite positive inner mass as a recursive functional\<close>

theorem slp_left_branch_positive_inner_mass_finite_functional:
  fixes branch_dummy :: "'i::finite itself"
  assumes cutoff_measurable:
      "cutoff \<in> borel_measurable lborel"
    and potential_measurable:
      "potential \<in> borel_measurable lborel"
    and terminal_value_measurable:
      "terminal_value \<in> borel_measurable lborel"
    and output_factor_measurable:
      "output_factor \<in> borel_measurable lborel"
  shows
    "slp_left_branch_positive_inner_mass_finite TYPE('i) R cutoff potential
        terminal_value output_factor origin =
      slp_positive_branch_functional R cutoff potential
        (\<lambda>x. ennreal (norm (terminal_value x))) CARD('i) origin
        (\<lambda>x. ennreal (norm (output_factor x)))"
  apply (subst slp_left_branch_positive_inner_mass_finite_natural_list[
      OF cutoff_measurable potential_measurable terminal_value_measurable
        output_factor_measurable])
  by (rule slp_left_branch_positive_kernel_list_integral_functional_natural[
        OF cutoff_measurable potential_measurable terminal_value_measurable
          output_factor_measurable])

end
