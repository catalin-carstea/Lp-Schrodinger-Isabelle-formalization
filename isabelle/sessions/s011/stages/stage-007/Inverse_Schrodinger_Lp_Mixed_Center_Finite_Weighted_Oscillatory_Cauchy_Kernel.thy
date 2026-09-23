theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Oscillatory_Cauchy_Kernel
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_007.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Oscillatory_Cauchy_Integrable"
begin

section \<open>Weighted finite mixed oscillatory center kernel\<close>

definition slp_mixed_center_finite_weighted_oscillatory_kernel ::
    "('i::finite) itself \<Rightarrow> ('j::finite) itself \<Rightarrow> real \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      (slp_point \<Rightarrow> complex) \<Rightarrow>
      slp_point \<Rightarrow> complex"
where
  "slp_mixed_center_finite_weighted_oscillatory_kernel TYPE('i) TYPE('j)
      frequency root_weight left_cutoff left_potential left_terminal_value
      right_cutoff right_potential right_terminal_value center_factor center =
    integral\<^sup>L lborel
      (slp_mixed_center_finite_weighted_oscillatory_integrand frequency
        root_weight left_cutoff left_potential left_terminal_value right_cutoff
        right_potential right_terminal_value center_factor center ::
        ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"

theorem slp_mixed_center_finite_weighted_absolute_fiber_mass_measurable:
  assumes root_weight_measurable:
      "root_weight \<in> borel_measurable lborel"
    and left_cutoff_measurable:
      "left_cutoff \<in> borel_measurable lborel"
    and left_potential_measurable:
      "left_potential \<in> borel_measurable lborel"
    and left_terminal_measurable:
      "left_terminal_value \<in> borel_measurable lborel"
    and right_cutoff_measurable:
      "right_cutoff \<in> borel_measurable lborel"
    and right_potential_measurable:
      "right_potential \<in> borel_measurable lborel"
    and right_terminal_measurable:
      "right_terminal_value \<in> borel_measurable lborel"
    and center_factor_measurable:
      "center_factor \<in> borel_measurable lborel"
  shows
    "(\<lambda>center.
      slp_mixed_center_finite_weighted_absolute_fiber_mass
        TYPE('i::finite) TYPE('j::finite) root_weight left_cutoff
        left_potential left_terminal_value right_cutoff right_potential
        right_terminal_value center_factor center) \<in> borel_measurable lborel"
proof -
  have amplitude_lborel_measurable:
      "((\<lambda>z :: slp_point \<times>
          ('i, 'j) slp_mixed_center_finite_coordinates.
        slp_mixed_center_finite_weighted_complex_amplitude root_weight
          left_cutoff left_potential left_terminal_value right_cutoff
          right_potential right_terminal_value center_factor
          (fst z) (snd z))) \<in> borel_measurable lborel"
    by (rule
      slp_mixed_center_finite_weighted_complex_amplitude_measurable[OF
        root_weight_measurable left_cutoff_measurable
        left_potential_measurable left_terminal_measurable
        right_cutoff_measurable right_potential_measurable
        right_terminal_measurable center_factor_measurable])
  have amplitude_measurable:
      "case_prod
        (slp_mixed_center_finite_weighted_complex_amplitude root_weight
          left_cutoff left_potential left_terminal_value right_cutoff
          right_potential right_terminal_value center_factor ::
          slp_point \<Rightarrow>
            ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)
        \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    using amplitude_lborel_measurable
    by (simp only: lborel_prod split_beta')
  have absolute_measurable:
      "case_prod
        (\<lambda>center (coordinates ::
            ('i, 'j) slp_mixed_center_finite_coordinates).
          ennreal (cmod
            (slp_mixed_center_finite_weighted_complex_amplitude root_weight
              left_cutoff left_potential left_terminal_value right_cutoff
              right_potential right_terminal_value center_factor center
              coordinates)))
        \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    using amplitude_measurable by measurable
  have parameter_measurable:
      "(\<lambda>center.
        nn_integral lborel (\<lambda>coordinates ::
            ('i, 'j) slp_mixed_center_finite_coordinates.
          ennreal (cmod
            (slp_mixed_center_finite_weighted_complex_amplitude root_weight
              left_cutoff left_potential left_terminal_value right_cutoff
              right_potential right_terminal_value center_factor center
              coordinates)))) \<in> borel_measurable lborel"
    by (rule lborel.borel_measurable_nn_integral[OF absolute_measurable])
  show ?thesis
    using parameter_measurable
    unfolding slp_mixed_center_finite_weighted_absolute_fiber_mass_def .
qed

theorem slp_mixed_center_finite_weighted_oscillatory_kernel_properties:
  assumes root_weight_measurable:
      "root_weight \<in> borel_measurable lborel"
    and left_cutoff_measurable:
      "left_cutoff \<in> borel_measurable lborel"
    and left_potential_measurable:
      "left_potential \<in> borel_measurable lborel"
    and left_terminal_measurable:
      "left_terminal_value \<in> borel_measurable lborel"
    and right_cutoff_measurable:
      "right_cutoff \<in> borel_measurable lborel"
    and right_potential_measurable:
      "right_potential \<in> borel_measurable lborel"
    and right_terminal_measurable:
      "right_terminal_value \<in> borel_measurable lborel"
    and center_factor_measurable:
      "center_factor \<in> borel_measurable lborel"
    and amplitude_integrable:
      "AE center in lborel.
        integrable lborel
          (slp_mixed_center_finite_weighted_complex_amplitude root_weight
            left_cutoff left_potential left_terminal_value right_cutoff
            right_potential right_terminal_value center_factor center ::
            ('i::finite, 'j::finite)
              slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
  shows
    "(slp_mixed_center_finite_weighted_oscillatory_kernel
        TYPE('i) TYPE('j) frequency root_weight left_cutoff left_potential
        left_terminal_value right_cutoff right_potential right_terminal_value
        center_factor) \<in> borel_measurable lborel"
    and
    "AE center in lborel.
      ennreal (norm_class.norm
        (slp_mixed_center_finite_weighted_oscillatory_kernel
          TYPE('i) TYPE('j) frequency root_weight left_cutoff left_potential
          left_terminal_value right_cutoff right_potential
          right_terminal_value center_factor center)) \<le>
      slp_mixed_center_finite_weighted_absolute_fiber_mass
        TYPE('i) TYPE('j) root_weight left_cutoff left_potential
        left_terminal_value right_cutoff right_potential right_terminal_value
        center_factor center"
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
        slp_mixed_center_finite_weighted_complex_amplitude root_weight
          left_cutoff left_potential left_terminal_value right_cutoff
          right_potential right_terminal_value center_factor
          (fst z) (snd z))) \<in> borel_measurable lborel"
    by (rule
      slp_mixed_center_finite_weighted_complex_amplitude_measurable[OF
        root_weight_measurable left_cutoff_measurable
        left_potential_measurable left_terminal_measurable
        right_cutoff_measurable right_potential_measurable
        right_terminal_measurable center_factor_measurable])
  have amplitude_measurable:
      "case_prod
        (slp_mixed_center_finite_weighted_complex_amplitude root_weight
          left_cutoff left_potential left_terminal_value right_cutoff
          right_potential right_terminal_value center_factor ::
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
      "(slp_mixed_center_finite_weighted_oscillatory_kernel
          TYPE('i) TYPE('j) frequency root_weight left_cutoff left_potential
          left_terminal_value right_cutoff right_potential
          right_terminal_value center_factor) \<in> borel_measurable lborel"
    using generic(1)
    unfolding slp_mixed_center_finite_weighted_oscillatory_kernel_def
      slp_mixed_center_finite_weighted_oscillatory_integrand_def
      slp_parameterized_real_phase_fiber_integral_def
      slp_parameterized_complex_fiber_integral_def .
  from generic(2) show
      "AE center in lborel.
        ennreal (norm_class.norm
          (slp_mixed_center_finite_weighted_oscillatory_kernel
            TYPE('i) TYPE('j) frequency root_weight left_cutoff left_potential
            left_terminal_value right_cutoff right_potential
            right_terminal_value center_factor center)) \<le>
        slp_mixed_center_finite_weighted_absolute_fiber_mass
          TYPE('i) TYPE('j) root_weight left_cutoff left_potential
          left_terminal_value right_cutoff right_potential
          right_terminal_value center_factor center"
    unfolding slp_mixed_center_finite_weighted_oscillatory_kernel_def
      slp_mixed_center_finite_weighted_oscillatory_integrand_def
      slp_parameterized_real_phase_fiber_integral_def
      slp_parameterized_complex_fiber_integral_def
      slp_parameterized_complex_absolute_fiber_mass_def
      slp_mixed_center_finite_weighted_absolute_fiber_mass_def .
qed

context aim_planar_riesz_hls_cauchy
begin

theorem slp_mixed_center_finite_weighted_oscillatory_cauchy_kernel_properties:
  fixes B C D p frequency :: real
    and X :: "slp_point set"
    and root_weight cutoff left_potential right_potential center_factor ::
      slp_scalar_field
    and left_orientation right_orientation :: slp_cauchy_orientation
  assumes B_nonnegative: "0 \<le> B"
    and C_nonnegative: "0 \<le> C"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and center_factor_measurable:
      "center_factor \<in> borel_measurable lborel"
    and left_potential_lp: "aim_complex_lp_on_plane p left_potential"
    and right_potential_lp: "aim_complex_lp_on_plane p right_potential"
    and root_weight_lp: "aim_complex_lp_on_plane p root_weight"
    and root_weight_outside:
      "\<And>x. x \<notin> X \<Longrightarrow> root_weight x = 0"
    and cutoff_bound: "\<And>x. cmod (cutoff x) \<le> C"
    and center_factor_bound: "\<And>x. cmod (center_factor x) \<le> D"
    and root_support:
      "\<And>x. root_weight x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and cutoff_support:
      "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and left_potential_support:
      "\<And>x. left_potential x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and right_potential_support:
      "\<And>x. right_potential x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
  shows
    "(slp_mixed_center_finite_weighted_oscillatory_kernel
        TYPE('i::finite) TYPE('j::finite) frequency root_weight cutoff
        left_potential (slp_cauchy_transform left_orientation left_potential)
        cutoff right_potential
        (slp_cauchy_transform right_orientation right_potential)
        center_factor) \<in> borel_measurable lborel"
    and
    "AE center in lborel.
      ennreal (norm_class.norm
        (slp_mixed_center_finite_weighted_oscillatory_kernel
          TYPE('i) TYPE('j) frequency root_weight cutoff left_potential
          (slp_cauchy_transform left_orientation left_potential) cutoff
          right_potential
          (slp_cauchy_transform right_orientation right_potential)
          center_factor center)) \<le>
      slp_mixed_center_finite_weighted_absolute_fiber_mass
        TYPE('i) TYPE('j) root_weight cutoff left_potential
        (slp_cauchy_transform left_orientation left_potential) cutoff
        right_potential
        (slp_cauchy_transform right_orientation right_potential)
        center_factor center"
proof -
  let ?left_terminal =
    "slp_cauchy_transform left_orientation left_potential"
  let ?right_terminal =
    "slp_cauchy_transform right_orientation right_potential"
  have root_weight_measurable:
      "root_weight \<in> borel_measurable lborel"
    using root_weight_lp unfolding aim_complex_lp_on_plane_def by blast
  have left_potential_measurable:
      "left_potential \<in> borel_measurable lborel"
    using left_potential_lp unfolding aim_complex_lp_on_plane_def by blast
  have right_potential_measurable:
      "right_potential \<in> borel_measurable lborel"
    using right_potential_lp unfolding aim_complex_lp_on_plane_def by blast
  have left_terminal_measurable:
      "?left_terminal \<in> borel_measurable lborel"
    by (rule slp_cauchy_transform_measurable_below_two[OF
          p_lower p_upper left_potential_lp])
  have right_terminal_measurable:
      "?right_terminal \<in> borel_measurable lborel"
    by (rule slp_cauchy_transform_measurable_below_two[OF
          p_lower p_upper right_potential_lp])
  have amplitude_integrable:
      "AE center in lborel.
        integrable lborel
          (slp_mixed_center_finite_weighted_complex_amplitude root_weight
            cutoff left_potential ?left_terminal cutoff right_potential
            ?right_terminal center_factor center ::
            ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
    by (rule
      slp_mixed_center_finite_weighted_amplitude_cauchy_fiber_integrable[OF
        B_nonnegative C_nonnegative p_lower p_upper X_measurable X_bounded
        cutoff_measurable center_factor_measurable left_potential_lp
        right_potential_lp root_weight_lp root_weight_outside cutoff_bound
        center_factor_bound root_support cutoff_support left_potential_support
        right_potential_support])
  note properties =
    slp_mixed_center_finite_weighted_oscillatory_kernel_properties[OF
      root_weight_measurable cutoff_measurable left_potential_measurable
      left_terminal_measurable cutoff_measurable right_potential_measurable
      right_terminal_measurable center_factor_measurable amplitude_integrable,
      where frequency = frequency]
  show
      "(slp_mixed_center_finite_weighted_oscillatory_kernel
          TYPE('i) TYPE('j) frequency root_weight cutoff left_potential
          ?left_terminal cutoff right_potential ?right_terminal center_factor)
        \<in> borel_measurable lborel"
    by (rule properties(1))
  show
      "AE center in lborel.
        ennreal (norm_class.norm
          (slp_mixed_center_finite_weighted_oscillatory_kernel
            TYPE('i) TYPE('j) frequency root_weight cutoff left_potential
            ?left_terminal cutoff right_potential ?right_terminal
            center_factor center)) \<le>
        slp_mixed_center_finite_weighted_absolute_fiber_mass
          TYPE('i) TYPE('j) root_weight cutoff left_potential ?left_terminal
          cutoff right_potential ?right_terminal center_factor center"
    by (rule properties(2))
qed

end

end
