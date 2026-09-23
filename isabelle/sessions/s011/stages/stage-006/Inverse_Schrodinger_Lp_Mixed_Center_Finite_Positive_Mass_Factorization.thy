theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Positive_Mass_Factorization
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_006.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Positive_Coordinate_Factorization"
begin

section \<open>Global finite mixed positive center-mass factorization\<close>

theorem slp_mixed_center_finite_positive_mass_factorization:
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
          slp_left_branch_positive_inner_mass_finite TYPE('i) R
            left_cutoff left_potential (\<lambda>_. 1) (\<lambda>_. 1) root *
          slp_left_branch_positive_inner_mass_finite TYPE('j) R
            right_cutoff right_potential (\<lambda>_. 1) (\<lambda>_. 1) root)"
proof -
  note center_to_coordinates =
    slp_mixed_center_finite_positive_mass_tonelli[
      OF root_weight_measurable left_cutoff_measurable
        left_potential_measurable right_cutoff_measurable
        right_potential_measurable,
      where R = R and 'i = 'i and 'j = 'j]
  note coordinates_to_root =
    slp_mixed_center_finite_positive_coordinate_factorization[
      OF root_weight_measurable left_cutoff_measurable
        left_potential_measurable right_cutoff_measurable
        right_potential_measurable,
      where R = R and 'i = 'i and 'j = 'j]
  show ?thesis
    using trans[OF center_to_coordinates coordinates_to_root] .
qed

end
