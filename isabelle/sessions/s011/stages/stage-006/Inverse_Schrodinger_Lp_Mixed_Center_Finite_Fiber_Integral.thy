theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Fiber_Integral
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_005.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Oscillatory_Integrand"
begin

section \<open>Guarded finite mixed fiber integral\<close>

definition slp_mixed_center_finite_fiber_integral ::
    "('i::finite) itself \<Rightarrow> ('j::finite) itself \<Rightarrow>
      real \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      slp_point \<Rightarrow> complex"
where
  "slp_mixed_center_finite_fiber_integral TYPE('i) TYPE('j) frequency
      root_weight left_cutoff left_potential right_cutoff right_potential
      center =
    slp_parameterized_real_phase_fiber_integral frequency
      (slp_mixed_center_finite_residual ::
        slp_point \<Rightarrow>
          ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> real)
      (slp_mixed_center_finite_complex_amplitude root_weight left_cutoff
        left_potential right_cutoff right_potential ::
        slp_point \<Rightarrow>
          ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)
      center"

definition slp_mixed_center_finite_absolute_fiber_mass ::
    "('i::finite) itself \<Rightarrow> ('j::finite) itself \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      slp_point \<Rightarrow> ennreal"
where
  "slp_mixed_center_finite_absolute_fiber_mass TYPE('i) TYPE('j) root_weight
      left_cutoff left_potential right_cutoff right_potential center =
    slp_parameterized_complex_absolute_fiber_mass
      (slp_mixed_center_finite_complex_amplitude root_weight left_cutoff
        left_potential right_cutoff right_potential ::
        slp_point \<Rightarrow>
          ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)
      center"

theorem slp_mixed_center_finite_fiber_integral_measurable_and_bound:
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
    and amplitude_integrable:
      "AE center in lborel.
        integrable lborel
          (slp_mixed_center_finite_complex_amplitude root_weight left_cutoff
            left_potential right_cutoff right_potential center ::
            ('i::finite, 'j::finite) slp_mixed_center_finite_coordinates
              \<Rightarrow> complex)"
  shows
      "(\<lambda>center :: slp_point.
      slp_mixed_center_finite_fiber_integral TYPE('i) TYPE('j) frequency
        root_weight left_cutoff left_potential right_cutoff right_potential
        center :: complex)
      \<in> borel_measurable lborel"
    and
    "AE center in lborel.
      ennreal (norm_class.norm
        (slp_mixed_center_finite_fiber_integral TYPE('i) TYPE('j) frequency
          root_weight left_cutoff left_potential right_cutoff right_potential
          center)) \<le>
      slp_mixed_center_finite_absolute_fiber_mass TYPE('i) TYPE('j)
        root_weight left_cutoff left_potential right_cutoff right_potential
        center"
proof -
  have phase_measurable:
      "case_prod (slp_mixed_center_finite_residual ::
          slp_point \<Rightarrow>
            ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> real)
        \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    by (rule slp_mixed_center_finite_residual_measurable)
  have amplitude_lborel_measurable:
      "((\<lambda>z :: slp_point \<times>
          ('i, 'j) slp_mixed_center_finite_coordinates.
        slp_mixed_center_finite_complex_amplitude root_weight left_cutoff
          left_potential right_cutoff right_potential (fst z) (snd z)))
        \<in> borel_measurable lborel"
    by (rule slp_mixed_center_finite_complex_amplitude_measurable[OF
          root_weight_measurable left_cutoff_measurable
          left_potential_measurable right_cutoff_measurable
          right_potential_measurable])
  have amplitude_measurable:
      "case_prod (slp_mixed_center_finite_complex_amplitude root_weight
          left_cutoff left_potential right_cutoff right_potential ::
        slp_point \<Rightarrow>
          ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)
        \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    using amplitude_lborel_measurable
    by (simp only: lborel_prod split_beta')
  note generic =
    slp_parameterized_real_phase_fiber_integral_measurable_and_bound[OF
      phase_measurable amplitude_measurable amplitude_integrable,
      where frequency = frequency]
  show
      "(\<lambda>center :: slp_point.
        slp_mixed_center_finite_fiber_integral TYPE('i) TYPE('j) frequency
          root_weight left_cutoff left_potential right_cutoff right_potential
          center :: complex) \<in> borel_measurable lborel"
    using generic(1)
    unfolding slp_mixed_center_finite_fiber_integral_def .
  from generic(2) show
      "AE center in lborel.
        ennreal (norm_class.norm
          (slp_mixed_center_finite_fiber_integral TYPE('i) TYPE('j) frequency
            root_weight left_cutoff left_potential right_cutoff
            right_potential center)) \<le>
        slp_mixed_center_finite_absolute_fiber_mass TYPE('i) TYPE('j)
          root_weight left_cutoff left_potential right_cutoff right_potential
          center"
    unfolding slp_mixed_center_finite_fiber_integral_def
      slp_mixed_center_finite_absolute_fiber_mass_def .
qed

end
