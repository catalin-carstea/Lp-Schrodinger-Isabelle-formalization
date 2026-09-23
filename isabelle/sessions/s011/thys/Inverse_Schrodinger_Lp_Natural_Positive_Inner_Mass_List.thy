theory Inverse_Schrodinger_Lp_Natural_Positive_Inner_Mass_List
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Natural_Positive_Integrand_List"
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_One_Sided_Finite_Positive_Inner_Mass_Natural"
begin

section \<open>The complete natural positive inner mass in recursive list form\<close>

theorem slp_left_branch_positive_inner_mass_finite_natural_list:
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
      (\<integral>\<^sup>+ pos_natural. \<integral>\<^sup>+ neg_natural.
        \<integral>\<^sup>+ terminal.
          slp_left_branch_positive_kernel_list R cutoff potential
              terminal_value
              (map (\<lambda>k. (pos_natural k, neg_natural k))
                [0..<CARD('i)]) origin terminal *
            ennreal (norm (output_factor
              (slp_left_branch_output
                (map (\<lambda>k. (pos_natural k, neg_natural k))
                  [0..<CARD('i)]) terminal)))
          \<partial>lborel
        \<partial>(PiM {..<CARD('i)}
          (\<lambda>_::nat. (lborel :: slp_point measure)))
      \<partial>(PiM {..<CARD('i)}
        (\<lambda>_::nat. (lborel :: slp_point measure))))"
  by (simp only: slp_left_branch_positive_inner_mass_finite_natural[
        OF cutoff_measurable potential_measurable terminal_value_measurable
          output_factor_measurable]
      slp_left_branch_positive_natural_integrand_list)

end
