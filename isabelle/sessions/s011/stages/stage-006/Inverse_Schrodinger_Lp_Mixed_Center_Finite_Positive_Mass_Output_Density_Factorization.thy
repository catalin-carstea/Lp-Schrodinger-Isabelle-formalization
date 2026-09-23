theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Positive_Mass_Output_Density_Factorization
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_006.Inverse_Schrodinger_Lp_One_Sided_Finite_Unit_Inner_Mass_Output_Density"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_006.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Positive_Mass_Factorization"
begin

section \<open>Finite mixed positive mass through output densities\<close>

theorem slp_mixed_center_finite_positive_mass_output_density_factorization:
  assumes root_weight_measurable:
      "root_weight \<in> borel_measurable lborel"
    and left_cutoff_measurable:
      "left_cutoff \<in> borel_measurable lborel"
    and left_potential_measurable:
      "left_potential \<in> borel_measurable lborel"
    and right_cutoff_measurable:
      "right_cutoff \<in> borel_measurable lborel"
    and right_potential_measurable:
      "right_potential \<in> borel_measurable lborel"
  shows
    "nn_integral lborel (\<lambda>center.
        slp_mixed_center_finite_positive_fiber_mass TYPE('i::finite)
          TYPE('j::finite) R root_weight left_cutoff left_potential
          right_cutoff right_potential center) =
      nn_integral lborel (\<lambda>root.
        ennreal (cmod (root_weight root)) *
          nn_integral lborel
            (slp_positive_output_density R left_cutoff left_potential
              (\<lambda>_. 1) CARD('i) root) *
          nn_integral lborel
            (slp_positive_output_density R right_cutoff right_potential
              (\<lambda>_. 1) CARD('j) root))"
proof -
  note mass_factorization =
    slp_mixed_center_finite_positive_mass_factorization[
      OF root_weight_measurable left_cutoff_measurable
        left_potential_measurable right_cutoff_measurable
        right_potential_measurable,
      where R = R and 'i = 'i and 'j = 'j]
  have left_mass:
      "slp_left_branch_positive_inner_mass_finite TYPE('i) R left_cutoff
          left_potential (\<lambda>_. 1) (\<lambda>_. 1) root =
        nn_integral lborel
          (slp_positive_output_density R left_cutoff left_potential
            (\<lambda>_. 1) CARD('i) root)"
    for root
    by (rule slp_left_branch_positive_inner_mass_finite_unit_output_density[
          OF left_cutoff_measurable left_potential_measurable])
  have right_mass:
      "slp_left_branch_positive_inner_mass_finite TYPE('j) R right_cutoff
          right_potential (\<lambda>_. 1) (\<lambda>_. 1) root =
        nn_integral lborel
          (slp_positive_output_density R right_cutoff right_potential
            (\<lambda>_. 1) CARD('j) root)"
    for root
    by (rule slp_left_branch_positive_inner_mass_finite_unit_output_density[
          OF right_cutoff_measurable right_potential_measurable])
  show ?thesis
    using mass_factorization by (simp only: left_mass right_mass)
qed

end
