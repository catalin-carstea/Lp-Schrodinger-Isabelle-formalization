theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Positive_Fiber_Mass
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_007.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Positive_Weight"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_006.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Positive_Fiber_Mass"
begin

section \<open>Terminal- and center-weighted finite positive fiber mass\<close>

definition slp_mixed_center_finite_weighted_positive_fiber_mass ::
    "('i::finite) itself \<Rightarrow> ('j::finite) itself \<Rightarrow> real \<Rightarrow>
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
  "slp_mixed_center_finite_weighted_positive_fiber_mass TYPE('i) TYPE('j) R
      root_weight left_cutoff left_potential left_terminal_value right_cutoff
      right_potential right_terminal_value center_factor center =
    nn_integral lborel (\<lambda>coordinates ::
        ('i, 'j) slp_mixed_center_finite_coordinates.
      ennreal (cmod (root_weight (fst coordinates))) *
        slp_left_branch_positive_kernel_joint R left_cutoff left_potential
          left_terminal_value
          (fst (slp_mixed_center_finite_inserted_coordinates
            center coordinates)) *
        slp_left_branch_positive_kernel_joint R right_cutoff right_potential
          right_terminal_value
          (snd (slp_mixed_center_finite_inserted_coordinates
            center coordinates)) *
        ennreal (cmod (center_factor center)))"

theorem slp_mixed_center_finite_weighted_positive_fiber_mass_unit:
  "slp_mixed_center_finite_weighted_positive_fiber_mass TYPE('i::finite)
      TYPE('j::finite) R root_weight left_cutoff left_potential (\<lambda>_. 1)
      right_cutoff right_potential (\<lambda>_. 1) (\<lambda>_. 1) center =
    slp_mixed_center_finite_positive_fiber_mass TYPE('i) TYPE('j) R
      root_weight left_cutoff left_potential right_cutoff right_potential
      center"
  unfolding slp_mixed_center_finite_weighted_positive_fiber_mass_def
    slp_mixed_center_finite_positive_fiber_mass_def
  by simp

end
