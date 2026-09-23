theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Fiber_Mass_Domination
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_007.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Absolute_Fiber_Mass"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_007.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Positive_Majorant"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Supported weighted fiber-mass domination\<close>

theorem slp_mixed_center_finite_weighted_absolute_fiber_mass_le_positive:
  fixes left_dummy :: "'i::finite itself"
    and right_dummy :: "'j::finite itself"
    and B :: real
    and root_weight left_cutoff left_potential left_terminal_value
      right_cutoff right_potential right_terminal_value center_factor ::
      "slp_point \<Rightarrow> complex"
    and center :: slp_point
  assumes B_nonnegative: "0 \<le> B"
    and root_support:
      "\<And>x. root_weight x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and left_cutoff_support:
      "\<And>x. left_cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and left_potential_support:
      "\<And>x. left_potential x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and right_cutoff_support:
      "\<And>x. right_cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and right_potential_support:
      "\<And>x. right_potential x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
  shows
    "slp_mixed_center_finite_weighted_absolute_fiber_mass
        TYPE('i) TYPE('j) root_weight left_cutoff left_potential
        left_terminal_value right_cutoff right_potential right_terminal_value
        center_factor center \<le>
      slp_mixed_center_finite_weighted_positive_fiber_mass
        TYPE('i) TYPE('j) (2 * B) root_weight left_cutoff left_potential
        left_terminal_value right_cutoff right_potential right_terminal_value
        center_factor center"
  unfolding slp_mixed_center_finite_weighted_absolute_fiber_mass_def
    slp_mixed_center_finite_weighted_positive_fiber_mass_def
  apply (rule nn_integral_mono)
  by (rule
    slp_mixed_center_finite_weighted_complex_amplitude_positive_majorant[OF
      B_nonnegative root_support left_cutoff_support left_potential_support
      right_cutoff_support right_potential_support])

theorem slp_mixed_center_finite_weighted_absolute_fiber_mass_density_bound:
  fixes left_dummy :: "'i::finite itself"
    and right_dummy :: "'j::finite itself"
    and B :: real
    and root_weight cutoff left_potential left_terminal_value
      right_potential right_terminal_value center_factor ::
      "slp_point \<Rightarrow> complex"
    and center :: slp_point
  assumes B_nonnegative: "0 \<le> B"
    and root_weight_measurable[measurable]:
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
    and root_support:
      "\<And>x. root_weight x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and cutoff_support:
      "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and left_potential_support:
      "\<And>x. left_potential x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and right_potential_support:
      "\<And>x. right_potential x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
  shows
    "slp_mixed_center_finite_weighted_absolute_fiber_mass
        TYPE('i) TYPE('j) root_weight cutoff left_potential
        left_terminal_value cutoff right_potential right_terminal_value
        center_factor center \<le>
      ennreal (cmod (center_factor center)) *
        slp_mixed_center_density (2 * B) cutoff left_potential
          right_potential
          (\<lambda>x. ennreal (cmod (left_terminal_value x)))
          (\<lambda>x. ennreal (cmod (right_terminal_value x)))
          CARD('i) CARD('j) root_weight center"
proof -
  have majorant:
      "slp_mixed_center_finite_weighted_absolute_fiber_mass
          TYPE('i) TYPE('j) root_weight cutoff left_potential
          left_terminal_value cutoff right_potential right_terminal_value
          center_factor center \<le>
        slp_mixed_center_finite_weighted_positive_fiber_mass
          TYPE('i) TYPE('j) (2 * B) root_weight cutoff left_potential
          left_terminal_value cutoff right_potential right_terminal_value
          center_factor center"
    by (rule
      slp_mixed_center_finite_weighted_absolute_fiber_mass_le_positive[OF
        B_nonnegative root_support cutoff_support left_potential_support
        cutoff_support right_potential_support])
  note density =
    slp_mixed_center_finite_weighted_positive_fiber_mass_density[
      where R = "2 * B" and root_weight = root_weight and cutoff = cutoff
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
    using majorant density by simp
qed

end
