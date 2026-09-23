theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Absolute_Fiber_Mass
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_007.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Positive_Fiber_Mass_Density"
begin

section \<open>Absolute fiber mass of the weighted finite mixed amplitude\<close>

definition slp_mixed_center_finite_weighted_absolute_fiber_mass ::
    "('i::finite) itself \<Rightarrow> ('j::finite) itself \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      slp_point \<Rightarrow> ennreal"
where
  "slp_mixed_center_finite_weighted_absolute_fiber_mass TYPE('i) TYPE('j)
      root_weight left_cutoff left_potential left_terminal_value right_cutoff
      right_potential right_terminal_value center_factor center =
    nn_integral lborel (\<lambda>coordinates ::
        ('i, 'j) slp_mixed_center_finite_coordinates.
      ennreal (cmod
        (slp_mixed_center_finite_weighted_complex_amplitude root_weight
          left_cutoff left_potential left_terminal_value right_cutoff
          right_potential right_terminal_value center_factor center
          coordinates)))"

theorem slp_mixed_center_finite_weighted_absolute_fiber_mass_density:
  fixes left_dummy :: "'i::finite itself"
    and right_dummy :: "'j::finite itself"
    and R :: real
    and root_weight cutoff left_potential left_terminal_value
      right_potential right_terminal_value center_factor ::
        "slp_point \<Rightarrow> complex"
    and center :: slp_point
  assumes root_weight_measurable[measurable]:
      "root_weight \<in> borel_measurable lborel"
    and cutoff_measurable[measurable]:
      "cutoff \<in> borel_measurable lborel"
    and left_potential_measurable[measurable]:
      "left_potential \<in> borel_measurable lborel"
    and left_terminal_measurable[measurable]:
      "left_terminal_value \<in> borel_measurable lborel"
    and right_potential_measurable[measurable]:
      "right_potential \<in> borel_measurable lborel"
    and right_terminal_measurable[measurable]:
      "right_terminal_value \<in> borel_measurable lborel"
    and left_chain:
      "\<And>coordinates :: ('i, 'j) slp_mixed_center_finite_coordinates.
        slp_left_branch_radius_chain_joint R
          (fst (slp_mixed_center_finite_inserted_coordinates
            center coordinates))"
    and right_chain:
      "\<And>coordinates :: ('i, 'j) slp_mixed_center_finite_coordinates.
        slp_left_branch_radius_chain_joint R
          (snd (slp_mixed_center_finite_inserted_coordinates
            center coordinates))"
  shows
    "slp_mixed_center_finite_weighted_absolute_fiber_mass
        TYPE('i) TYPE('j) root_weight cutoff left_potential
        left_terminal_value cutoff right_potential right_terminal_value
        center_factor center =
      ennreal (cmod (center_factor center)) *
        slp_mixed_center_density R cutoff left_potential right_potential
          (\<lambda>x. ennreal (cmod (left_terminal_value x)))
          (\<lambda>x. ennreal (cmod (right_terminal_value x)))
          CARD('i) CARD('j) root_weight center"
proof -
  have absolute_eq_positive:
      "slp_mixed_center_finite_weighted_absolute_fiber_mass
          TYPE('i) TYPE('j) root_weight cutoff left_potential
          left_terminal_value cutoff right_potential right_terminal_value
          center_factor center =
        slp_mixed_center_finite_weighted_positive_fiber_mass
          TYPE('i) TYPE('j) R root_weight cutoff left_potential
          left_terminal_value cutoff right_potential right_terminal_value
          center_factor center"
    unfolding slp_mixed_center_finite_weighted_absolute_fiber_mass_def
      slp_mixed_center_finite_weighted_positive_fiber_mass_def
    apply (rule nn_integral_cong)
    by (rule
      slp_mixed_center_finite_weighted_complex_amplitude_positive_weight[OF
        left_chain right_chain])
  note density =
    slp_mixed_center_finite_weighted_positive_fiber_mass_density[
      where R = R and root_weight = root_weight and cutoff = cutoff
        and left_potential = left_potential
        and left_terminal_value = left_terminal_value
        and right_potential = right_potential
        and right_terminal_value = right_terminal_value
        and center_factor = center_factor and center = center
        and 'i = 'i and 'j = 'j,
      OF root_weight_measurable cutoff_measurable
        left_potential_measurable left_terminal_measurable
        right_potential_measurable right_terminal_measurable]
  show ?thesis
    using trans[OF absolute_eq_positive density] .
qed

end
