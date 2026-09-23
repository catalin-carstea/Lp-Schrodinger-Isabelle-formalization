theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Positive_Fiber_Mass
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_006.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Positive_Majorant"
begin

section \<open>Positive fiber mass for the finite mixed-center amplitude\<close>

definition slp_mixed_center_finite_positive_fiber_mass ::
    "('i::finite) itself \<Rightarrow> ('j::finite) itself \<Rightarrow> real \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      slp_point \<Rightarrow> ennreal"
where
  "slp_mixed_center_finite_positive_fiber_mass TYPE('i) TYPE('j) R
      root_weight left_cutoff left_potential right_cutoff right_potential
      center =
    nn_integral lborel (\<lambda>coordinates ::
        ('i, 'j) slp_mixed_center_finite_coordinates.
      ennreal (cmod (root_weight (fst coordinates))) *
        slp_left_branch_positive_kernel_joint R left_cutoff left_potential
          (\<lambda>_. 1)
          (fst (slp_mixed_center_finite_inserted_coordinates
            center coordinates)) *
        slp_left_branch_positive_kernel_joint R right_cutoff right_potential
          (\<lambda>_. 1)
          (snd (slp_mixed_center_finite_inserted_coordinates
            center coordinates)))"

theorem slp_mixed_center_finite_absolute_fiber_mass_le_positive:
  fixes B :: real
    and root_weight left_cutoff left_potential right_cutoff right_potential ::
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
    "slp_mixed_center_finite_absolute_fiber_mass TYPE('i::finite)
        TYPE('j::finite) root_weight left_cutoff left_potential right_cutoff
        right_potential center \<le>
      slp_mixed_center_finite_positive_fiber_mass TYPE('i) TYPE('j) (2 * B)
        root_weight left_cutoff left_potential right_cutoff right_potential
        center"
  unfolding slp_mixed_center_finite_absolute_fiber_mass_def
    slp_parameterized_complex_absolute_fiber_mass_def
    slp_mixed_center_finite_positive_fiber_mass_def
proof (rule nn_integral_mono)
  fix coordinates ::
    "('i, 'j) slp_mixed_center_finite_coordinates"
  show
    "ennreal (norm_class.norm
        (slp_mixed_center_finite_complex_amplitude root_weight left_cutoff
          left_potential right_cutoff right_potential center coordinates)) \<le>
      ennreal (cmod (root_weight (fst coordinates))) *
        slp_left_branch_positive_kernel_joint (2 * B) left_cutoff
          left_potential (\<lambda>_. 1)
          (fst (slp_mixed_center_finite_inserted_coordinates
            center coordinates)) *
        slp_left_branch_positive_kernel_joint (2 * B) right_cutoff
          right_potential (\<lambda>_. 1)
          (snd (slp_mixed_center_finite_inserted_coordinates
            center coordinates))"
    by (rule slp_mixed_center_finite_complex_amplitude_positive_majorant[OF
          B_nonnegative root_support left_cutoff_support
          left_potential_support right_cutoff_support
          right_potential_support])
qed

end
