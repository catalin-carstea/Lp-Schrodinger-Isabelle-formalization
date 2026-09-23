theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Cauchy_Difference_Global_Decay
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_008.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Cauchy_Difference_Measure_Interfaces"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_007.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Oscillatory_Cauchy_Global_Decay"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Global decay of the exact primitive differences\<close>

lemma slp_mixed_center_finite_weighted_oscillatory_fiber_integrable:
  fixes phase :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space \<Rightarrow> real"
    and amplitude :: "'a \<Rightarrow> 'b \<Rightarrow> complex"
  assumes phase_measurable:
      "case_prod phase \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    and amplitude_integrable:
      "AE center in lborel.
        integrable lborel (amplitude center)"
  shows
      "AE center in lborel.
        integrable lborel
          (slp_parameterized_real_phase_integrand frequency phase amplitude
            center)"
proof -
  from amplitude_integrable show ?thesis
  proof eventually_elim
    fix center
    assume center_integrable: "integrable lborel (amplitude center)"
    have center_space: "center \<in> space (lborel :: 'a measure)"
      by simp
    have phase_section_measurable:
        "phase center \<in> borel_measurable lborel"
    proof -
      note raw = measurable_compose_Pair1[OF center_space phase_measurable]
      show ?thesis using raw by simp
    qed
    have scaled_phase_measurable:
        "(\<lambda>fiber. frequency * phase center fiber)
          \<in> borel_measurable lborel"
      using phase_section_measurable by measurable
    show "integrable lborel
        (slp_parameterized_real_phase_integrand frequency phase amplitude
          center)"
      unfolding slp_parameterized_real_phase_integrand_def
      by (rule slp_unit_modulus_real_phase_integrable[OF
            center_integrable scaled_phase_measurable])
  qed
qed

theorem slp_mixed_center_finite_weighted_terminal_center_diff_global_expansion_from_masses:
  assumes root_weight_measurable:
      "root_weight \<in> borel_measurable lborel"
    and left_cutoff_measurable:
      "left_cutoff \<in> borel_measurable lborel"
    and left_potential_measurable:
      "left_potential \<in> borel_measurable lborel"
    and left_terminal_measurable:
      "left_terminal \<in> borel_measurable lborel"
    and right_cutoff_measurable:
      "right_cutoff \<in> borel_measurable lborel"
    and right_potential_measurable:
      "right_potential \<in> borel_measurable lborel"
    and right_terminal_measurable:
      "right_terminal \<in> borel_measurable lborel"
    and center_factor_measurable:
      "center_factor \<in> borel_measurable lborel"
    and terminal_terminal_mass_finite:
      "(\<integral>\<^sup>+ center.
        slp_mixed_center_finite_weighted_absolute_fiber_mass
          TYPE('i::finite) TYPE('j::finite) root_weight left_cutoff
          left_potential left_terminal right_cutoff right_potential
          right_terminal center_factor center \<partial>lborel) < top_class.top"
    and left_cross_mass_finite:
      "(\<integral>\<^sup>+ center.
        slp_mixed_center_finite_weighted_absolute_fiber_mass
          TYPE('i) TYPE('j) root_weight left_cutoff left_potential
          left_terminal right_cutoff right_potential (\<lambda>_. 1)
          (\<lambda>x. -(center_factor x * right_terminal x)) center
          \<partial>lborel) < top_class.top"
    and right_cross_mass_finite:
      "(\<integral>\<^sup>+ center.
        slp_mixed_center_finite_weighted_absolute_fiber_mass
          TYPE('i) TYPE('j) root_weight left_cutoff left_potential (\<lambda>_. 1)
          right_cutoff right_potential right_terminal
          (\<lambda>x. -(center_factor x * left_terminal x)) center
          \<partial>lborel) < top_class.top"
    and unit_unit_mass_finite:
      "(\<integral>\<^sup>+ center.
        slp_mixed_center_finite_weighted_absolute_fiber_mass
          TYPE('i) TYPE('j) root_weight left_cutoff left_potential (\<lambda>_. 1)
          right_cutoff right_potential (\<lambda>_. 1)
          (\<lambda>x. center_factor x *
            (left_terminal x * right_terminal x)) center
          \<partial>lborel) < top_class.top"
  shows
    "integral\<^sup>L lborel
        (slp_mixed_center_finite_weighted_oscillatory_terminal_center_diff_kernel
          TYPE('i) TYPE('j) frequency root_weight left_cutoff left_potential
          left_terminal right_cutoff right_potential right_terminal
          center_factor) =
      integral\<^sup>L lborel
          (slp_mixed_center_finite_weighted_oscillatory_kernel
            TYPE('i) TYPE('j) frequency root_weight left_cutoff left_potential
            left_terminal right_cutoff right_potential right_terminal
            center_factor) +
      integral\<^sup>L lborel
          (slp_mixed_center_finite_weighted_oscillatory_kernel
            TYPE('i) TYPE('j) frequency root_weight left_cutoff left_potential
            left_terminal right_cutoff right_potential (\<lambda>_. 1)
            (\<lambda>x. -(center_factor x * right_terminal x))) +
      integral\<^sup>L lborel
          (slp_mixed_center_finite_weighted_oscillatory_kernel
            TYPE('i) TYPE('j) frequency root_weight left_cutoff left_potential
            (\<lambda>_. 1) right_cutoff right_potential right_terminal
            (\<lambda>x. -(center_factor x * left_terminal x))) +
      integral\<^sup>L lborel
          (slp_mixed_center_finite_weighted_oscillatory_kernel
            TYPE('i) TYPE('j) frequency root_weight left_cutoff left_potential
            (\<lambda>_. 1) right_cutoff right_potential (\<lambda>_. 1)
            (\<lambda>x. center_factor x *
              (left_terminal x * right_terminal x)))"
proof -
  let ?unit = "\<lambda>_ :: slp_point. (1 :: complex)"
  let ?left_center = "\<lambda>x. -(center_factor x * right_terminal x)"
  let ?right_center = "\<lambda>x. -(center_factor x * left_terminal x)"
  let ?unit_center = "\<lambda>x. center_factor x *
    (left_terminal x * right_terminal x)"
  let ?tt_mass = "slp_mixed_center_finite_weighted_absolute_fiber_mass
    TYPE('i) TYPE('j) root_weight left_cutoff left_potential left_terminal
    right_cutoff right_potential right_terminal center_factor"
  let ?lc_mass = "slp_mixed_center_finite_weighted_absolute_fiber_mass
    TYPE('i) TYPE('j) root_weight left_cutoff left_potential left_terminal
    right_cutoff right_potential ?unit ?left_center"
  let ?rc_mass = "slp_mixed_center_finite_weighted_absolute_fiber_mass
    TYPE('i) TYPE('j) root_weight left_cutoff left_potential ?unit
    right_cutoff right_potential right_terminal ?right_center"
  let ?uu_mass = "slp_mixed_center_finite_weighted_absolute_fiber_mass
    TYPE('i) TYPE('j) root_weight left_cutoff left_potential ?unit
    right_cutoff right_potential ?unit ?unit_center"
  let ?tt_kernel = "slp_mixed_center_finite_weighted_oscillatory_kernel
    TYPE('i) TYPE('j) frequency root_weight left_cutoff left_potential
    left_terminal right_cutoff right_potential right_terminal center_factor"
  let ?lc_kernel = "slp_mixed_center_finite_weighted_oscillatory_kernel
    TYPE('i) TYPE('j) frequency root_weight left_cutoff left_potential
    left_terminal right_cutoff right_potential ?unit ?left_center"
  let ?rc_kernel = "slp_mixed_center_finite_weighted_oscillatory_kernel
    TYPE('i) TYPE('j) frequency root_weight left_cutoff left_potential ?unit
    right_cutoff right_potential right_terminal ?right_center"
  let ?uu_kernel = "slp_mixed_center_finite_weighted_oscillatory_kernel
    TYPE('i) TYPE('j) frequency root_weight left_cutoff left_potential ?unit
    right_cutoff right_potential ?unit ?unit_center"
  have unit_measurable: "?unit \<in> borel_measurable lborel"
    by measurable
  have left_center_measurable: "?left_center \<in> borel_measurable lborel"
    using center_factor_measurable right_terminal_measurable by measurable
  have right_center_measurable: "?right_center \<in> borel_measurable lborel"
    using center_factor_measurable left_terminal_measurable by measurable
  have unit_center_measurable: "?unit_center \<in> borel_measurable lborel"
    using center_factor_measurable left_terminal_measurable
      right_terminal_measurable by measurable
  have mass_measurable:
      "?tt_mass \<in> borel_measurable lborel"
      "?lc_mass \<in> borel_measurable lborel"
      "?rc_mass \<in> borel_measurable lborel"
      "?uu_mass \<in> borel_measurable lborel"
    by (rule
          slp_mixed_center_finite_weighted_absolute_fiber_mass_measurable[OF
            root_weight_measurable left_cutoff_measurable
            left_potential_measurable left_terminal_measurable
            right_cutoff_measurable right_potential_measurable
            right_terminal_measurable center_factor_measurable],
        rule
          slp_mixed_center_finite_weighted_absolute_fiber_mass_measurable[OF
            root_weight_measurable left_cutoff_measurable
            left_potential_measurable left_terminal_measurable
            right_cutoff_measurable right_potential_measurable
            unit_measurable left_center_measurable],
        rule
          slp_mixed_center_finite_weighted_absolute_fiber_mass_measurable[OF
            root_weight_measurable left_cutoff_measurable
            left_potential_measurable unit_measurable right_cutoff_measurable
            right_potential_measurable right_terminal_measurable
            right_center_measurable],
        rule
          slp_mixed_center_finite_weighted_absolute_fiber_mass_measurable[OF
            root_weight_measurable left_cutoff_measurable
            left_potential_measurable unit_measurable right_cutoff_measurable
            right_potential_measurable unit_measurable
            unit_center_measurable])
  have amplitude_integrable:
      "AE center in lborel. integrable lborel
        (slp_mixed_center_finite_weighted_complex_amplitude root_weight
          left_cutoff left_potential left_terminal right_cutoff
          right_potential right_terminal center_factor center ::
          ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
      "AE center in lborel. integrable lborel
        (slp_mixed_center_finite_weighted_complex_amplitude root_weight
          left_cutoff left_potential left_terminal right_cutoff
          right_potential ?unit ?left_center center ::
          ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
      "AE center in lborel. integrable lborel
        (slp_mixed_center_finite_weighted_complex_amplitude root_weight
          left_cutoff left_potential ?unit right_cutoff right_potential
          right_terminal ?right_center center ::
          ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
      "AE center in lborel. integrable lborel
        (slp_mixed_center_finite_weighted_complex_amplitude root_weight
          left_cutoff left_potential ?unit right_cutoff right_potential
          ?unit ?unit_center center ::
          ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
    by (rule
          slp_mixed_center_finite_weighted_amplitude_fiber_integrable_from_mass[OF
            root_weight_measurable left_cutoff_measurable
            left_potential_measurable left_terminal_measurable
            right_cutoff_measurable right_potential_measurable
            right_terminal_measurable center_factor_measurable
            terminal_terminal_mass_finite],
        rule
          slp_mixed_center_finite_weighted_amplitude_fiber_integrable_from_mass[OF
            root_weight_measurable left_cutoff_measurable
            left_potential_measurable left_terminal_measurable
            right_cutoff_measurable right_potential_measurable unit_measurable
            left_center_measurable left_cross_mass_finite],
        rule
          slp_mixed_center_finite_weighted_amplitude_fiber_integrable_from_mass[OF
            root_weight_measurable left_cutoff_measurable
            left_potential_measurable unit_measurable right_cutoff_measurable
            right_potential_measurable right_terminal_measurable
            right_center_measurable right_cross_mass_finite],
        rule
          slp_mixed_center_finite_weighted_amplitude_fiber_integrable_from_mass[OF
            root_weight_measurable left_cutoff_measurable
            left_potential_measurable unit_measurable right_cutoff_measurable
            right_potential_measurable unit_measurable unit_center_measurable
            unit_unit_mass_finite])
  have fiber_integrable:
      "AE center in lborel.
        integrable lborel
          (slp_mixed_center_finite_weighted_oscillatory_integrand frequency
            root_weight left_cutoff left_potential left_terminal right_cutoff
            right_potential right_terminal center_factor center ::
            ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex) \<and>
        integrable lborel
          (slp_mixed_center_finite_weighted_oscillatory_integrand frequency
            root_weight left_cutoff left_potential left_terminal right_cutoff
            right_potential ?unit ?left_center center ::
            ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex) \<and>
        integrable lborel
          (slp_mixed_center_finite_weighted_oscillatory_integrand frequency
            root_weight left_cutoff left_potential ?unit right_cutoff
            right_potential right_terminal ?right_center center ::
            ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex) \<and>
        integrable lborel
          (slp_mixed_center_finite_weighted_oscillatory_integrand frequency
            root_weight left_cutoff left_potential ?unit right_cutoff
            right_potential ?unit ?unit_center center ::
            ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
  proof -
    have phase_measurable:
        "case_prod (slp_mixed_center_finite_residual ::
          slp_point \<Rightarrow>
            ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> real)
          \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
      by (rule slp_mixed_center_finite_residual_measurable)
    note fibers =
      slp_mixed_center_finite_weighted_oscillatory_fiber_integrable[OF
        phase_measurable amplitude_integrable(1), where frequency=frequency]
      slp_mixed_center_finite_weighted_oscillatory_fiber_integrable[OF
        phase_measurable amplitude_integrable(2), where frequency=frequency]
      slp_mixed_center_finite_weighted_oscillatory_fiber_integrable[OF
        phase_measurable amplitude_integrable(3), where frequency=frequency]
      slp_mixed_center_finite_weighted_oscillatory_fiber_integrable[OF
        phase_measurable amplitude_integrable(4), where frequency=frequency]
    from fibers show ?thesis
      unfolding slp_mixed_center_finite_weighted_oscillatory_integrand_def
      by eventually_elim blast
  qed
  have diff_measurable:
      "slp_mixed_center_finite_weighted_oscillatory_terminal_center_diff_kernel
        TYPE('i) TYPE('j) frequency root_weight left_cutoff left_potential
        left_terminal right_cutoff right_potential right_terminal center_factor
        \<in> borel_measurable lborel"
    by (rule
      slp_mixed_center_finite_weighted_oscillatory_terminal_center_diff_kernel_measurable[OF
        root_weight_measurable left_cutoff_measurable
        left_potential_measurable left_terminal_measurable
        right_cutoff_measurable right_potential_measurable
        right_terminal_measurable center_factor_measurable])
  note tt_properties =
    slp_mixed_center_finite_weighted_oscillatory_kernel_properties[OF
      root_weight_measurable left_cutoff_measurable left_potential_measurable
      left_terminal_measurable right_cutoff_measurable
      right_potential_measurable right_terminal_measurable
      center_factor_measurable amplitude_integrable(1),
      where frequency=frequency]
  note lc_properties =
    slp_mixed_center_finite_weighted_oscillatory_kernel_properties[OF
      root_weight_measurable left_cutoff_measurable left_potential_measurable
      left_terminal_measurable right_cutoff_measurable
      right_potential_measurable unit_measurable left_center_measurable
      amplitude_integrable(2), where frequency=frequency]
  note rc_properties =
    slp_mixed_center_finite_weighted_oscillatory_kernel_properties[OF
      root_weight_measurable left_cutoff_measurable left_potential_measurable
      unit_measurable right_cutoff_measurable right_potential_measurable
      right_terminal_measurable right_center_measurable
      amplitude_integrable(3), where frequency=frequency]
  note uu_properties =
    slp_mixed_center_finite_weighted_oscillatory_kernel_properties[OF
      root_weight_measurable left_cutoff_measurable left_potential_measurable
      unit_measurable right_cutoff_measurable right_potential_measurable
      unit_measurable unit_center_measurable amplitude_integrable(4),
      where frequency=frequency]
  have kernels_integrable:
      "integrable lborel ?tt_kernel"
      "integrable lborel ?lc_kernel"
      "integrable lborel ?rc_kernel"
      "integrable lborel ?uu_kernel"
    by (rule slp_integrable_from_ennreal_mass_bound[OF
          mass_measurable(1) terminal_terminal_mass_finite tt_properties(1)
          tt_properties(2)],
        rule slp_integrable_from_ennreal_mass_bound[OF
          mass_measurable(2) left_cross_mass_finite lc_properties(1)
          lc_properties(2)],
        rule slp_integrable_from_ennreal_mass_bound[OF
          mass_measurable(3) right_cross_mass_finite rc_properties(1)
          rc_properties(2)],
        rule slp_integrable_from_ennreal_mass_bound[OF
          mass_measurable(4) unit_unit_mass_finite uu_properties(1)
          uu_properties(2)])
  show ?thesis
    by (rule
      slp_mixed_center_finite_weighted_oscillatory_terminal_center_diff_global_expansion[OF
        fiber_integrable diff_measurable kernels_integrable(1)
        kernels_integrable(2) kernels_integrable(3) kernels_integrable(4)])
qed

context aim_planar_riesz_hls_cauchy
begin

theorem slp_mixed_center_finite_weighted_oscillatory_cauchy_center_diff_global_decay:
  fixes active_type ::
      "((unit + (((('i::finite) + 'i) + unit) + (('j::finite) + 'j)))
        \<times> bool) itself"
    and B C D p :: real
    and X :: "slp_point set"
    and phi root_weight cutoff left_potential right_potential ::
      slp_scalar_field
    and left_orientation right_orientation :: slp_cauchy_orientation
  assumes stationary_phase:
      "hormander_quadratic_stationary_phase_decay_claim active_type"
    and density: "evans_compact_smooth_l1_density_claim active_type"
    and B_nonnegative: "0 \<le> B"
    and C_nonnegative: "0 \<le> C"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
    and phi_test: "slp_test_function_on UNIV phi"
    and phi_bound: "\<And>x. cmod (phi x) \<le> D"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and left_potential_lp: "aim_complex_lp_on_plane p left_potential"
    and right_potential_lp: "aim_complex_lp_on_plane p right_potential"
    and root_weight_lp: "aim_complex_lp_on_plane p root_weight"
    and root_weight_outside:
      "\<And>x. x \<notin> X \<Longrightarrow> root_weight x = 0"
    and cutoff_bound: "\<And>x. cmod (cutoff x) \<le> C"
    and root_support:
      "\<And>x. root_weight x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and cutoff_support:
      "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and left_potential_support:
      "\<And>x. left_potential x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
    and right_potential_support:
      "\<And>x. right_potential x \<noteq> 0 \<Longrightarrow> norm x \<le> B"
  shows
    "((\<lambda>frequency.
      integral\<^sup>L lborel
        (slp_mixed_center_finite_weighted_oscillatory_terminal_center_diff_kernel
          TYPE('i) TYPE('j) frequency root_weight cutoff left_potential
          (slp_cauchy_transform left_orientation left_potential) cutoff
          right_potential
          (slp_cauchy_transform right_orientation right_potential) phi))
      \<longlongrightarrow> 0) at_top"
proof -
  let ?left_terminal =
    "slp_cauchy_transform left_orientation left_potential"
  let ?right_terminal =
    "slp_cauchy_transform right_orientation right_potential"
  let ?unit = "\<lambda>_ :: slp_point. (1 :: complex)"
  let ?left_center = "\<lambda>x. -(phi x * ?right_terminal x)"
  let ?right_center = "\<lambda>x. -(phi x * ?left_terminal x)"
  let ?unit_center = "\<lambda>x. phi x *
    (?left_terminal x * ?right_terminal x)"
  let ?tt_mass = "slp_mixed_center_finite_weighted_absolute_fiber_mass
    TYPE('i) TYPE('j) root_weight cutoff left_potential ?left_terminal
    cutoff right_potential ?right_terminal phi"
  let ?lc_mass = "slp_mixed_center_finite_weighted_absolute_fiber_mass
    TYPE('i) TYPE('j) root_weight cutoff left_potential ?left_terminal
    cutoff right_potential ?unit ?left_center"
  let ?rc_mass = "slp_mixed_center_finite_weighted_absolute_fiber_mass
    TYPE('i) TYPE('j) root_weight cutoff left_potential ?unit
    cutoff right_potential ?right_terminal ?right_center"
  let ?uu_mass = "slp_mixed_center_finite_weighted_absolute_fiber_mass
    TYPE('i) TYPE('j) root_weight cutoff left_potential ?unit
    cutoff right_potential ?unit ?unit_center"
  let ?full = "\<lambda>frequency. integral\<^sup>L lborel
    (slp_mixed_center_finite_weighted_oscillatory_terminal_center_diff_kernel
      TYPE('i) TYPE('j) frequency root_weight cutoff left_potential
      ?left_terminal cutoff right_potential ?right_terminal phi)"
  let ?tt = "\<lambda>frequency. integral\<^sup>L lborel
    (slp_mixed_center_finite_weighted_oscillatory_kernel
      TYPE('i) TYPE('j) frequency root_weight cutoff left_potential
      ?left_terminal cutoff right_potential ?right_terminal phi)"
  let ?lc = "\<lambda>frequency. integral\<^sup>L lborel
    (slp_mixed_center_finite_weighted_oscillatory_kernel
      TYPE('i) TYPE('j) frequency root_weight cutoff left_potential
      ?left_terminal cutoff right_potential ?unit ?left_center)"
  let ?rc = "\<lambda>frequency. integral\<^sup>L lborel
    (slp_mixed_center_finite_weighted_oscillatory_kernel
      TYPE('i) TYPE('j) frequency root_weight cutoff left_potential ?unit
      cutoff right_potential ?right_terminal ?right_center)"
  let ?uu = "\<lambda>frequency. integral\<^sup>L lborel
    (slp_mixed_center_finite_weighted_oscillatory_kernel
      TYPE('i) TYPE('j) frequency root_weight cutoff left_potential ?unit
      cutoff right_potential ?unit ?unit_center)"
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
  have phi_integrable: "integrable lborel phi"
    by (rule slp_test_function_integrable_bounded(1)[OF phi_test])
  have phi_measurable: "phi \<in> borel_measurable lborel"
    using phi_integrable unfolding integrable_iff_bounded by blast
  have tt_mass_finite: "nn_integral lborel ?tt_mass < top_class.top"
    by (rule
      slp_mixed_center_finite_weighted_absolute_mass_cauchy_finite[OF
        B_nonnegative C_nonnegative p_lower p_upper X_measurable X_bounded
        cutoff_measurable left_potential_lp right_potential_lp
        root_weight_lp root_weight_outside cutoff_bound phi_bound
        root_support cutoff_support left_potential_support
        right_potential_support])
  have lc_mass_finite: "nn_integral lborel ?lc_mass < top_class.top"
    by (rule
      slp_mixed_center_finite_weighted_absolute_mass_left_cross_finite[OF
        B_nonnegative C_nonnegative p_lower p_upper X_measurable X_bounded
        phi_test cutoff_measurable left_potential_lp right_potential_lp
        root_weight_lp root_weight_outside cutoff_bound root_support
        cutoff_support left_potential_support right_potential_support])
  have rc_mass_finite: "nn_integral lborel ?rc_mass < top_class.top"
    by (rule
      slp_mixed_center_finite_weighted_absolute_mass_right_cross_finite[OF
        B_nonnegative C_nonnegative p_lower p_upper X_measurable X_bounded
        phi_test cutoff_measurable left_potential_lp right_potential_lp
        root_weight_lp root_weight_outside cutoff_bound root_support
        cutoff_support left_potential_support right_potential_support])
  have uu_mass_finite: "nn_integral lborel ?uu_mass < top_class.top"
    by (rule
      slp_mixed_center_finite_weighted_absolute_mass_unit_unit_two_cauchy_finite[OF
        B_nonnegative C_nonnegative p_lower p_upper X_measurable X_bounded
        phi_test cutoff_measurable left_potential_lp right_potential_lp
        root_weight_lp root_weight_outside cutoff_bound root_support
        cutoff_support left_potential_support right_potential_support])
  have expansion: "\<And>frequency.
      ?full frequency =
        ?tt frequency + ?lc frequency + ?rc frequency + ?uu frequency"
    by (rule
      slp_mixed_center_finite_weighted_terminal_center_diff_global_expansion_from_masses[OF
        root_weight_measurable cutoff_measurable left_potential_measurable
        left_terminal_measurable cutoff_measurable right_potential_measurable
        right_terminal_measurable phi_measurable tt_mass_finite
        lc_mass_finite rc_mass_finite uu_mass_finite])
  have tt_decay: "(?tt \<longlongrightarrow> 0) at_top"
    by (rule
      slp_mixed_center_finite_weighted_oscillatory_cauchy_global_decay[OF
        stationary_phase density B_nonnegative C_nonnegative p_lower p_upper
        X_measurable X_bounded cutoff_measurable phi_measurable
        left_potential_lp right_potential_lp root_weight_lp
        root_weight_outside cutoff_bound phi_bound root_support cutoff_support
        left_potential_support right_potential_support])
  note cross_decay =
    slp_mixed_center_finite_weighted_oscillatory_cross_global_decay[OF
      stationary_phase density B_nonnegative C_nonnegative p_lower p_upper
      X_measurable X_bounded phi_test cutoff_measurable left_potential_lp
      right_potential_lp root_weight_lp root_weight_outside cutoff_bound
      root_support cutoff_support left_potential_support
      right_potential_support]
  have uu_decay: "(?uu \<longlongrightarrow> 0) at_top"
    by (rule
      slp_mixed_center_finite_weighted_oscillatory_unit_unit_global_decay[OF
        stationary_phase density B_nonnegative C_nonnegative p_lower p_upper
        X_measurable X_bounded phi_test cutoff_measurable left_potential_lp
        right_potential_lp root_weight_lp root_weight_outside cutoff_bound
        root_support cutoff_support left_potential_support
        right_potential_support])
  have sum_decay:
      "((\<lambda>frequency.
        ?tt frequency + ?lc frequency + ?rc frequency + ?uu frequency)
        \<longlongrightarrow> 0) at_top"
  proof -
    have first:
        "((\<lambda>frequency. ?tt frequency + ?lc frequency)
          \<longlongrightarrow> 0 + 0) at_top"
      by (rule tendsto_add[OF tt_decay cross_decay(1)])
    have second:
        "((\<lambda>frequency.
          (?tt frequency + ?lc frequency) + ?rc frequency)
          \<longlongrightarrow> (0 + 0) + 0) at_top"
      by (rule tendsto_add[OF first cross_decay(2)])
    have third:
        "((\<lambda>frequency.
          (?tt frequency + ?lc frequency) + ?rc frequency + ?uu frequency)
          \<longlongrightarrow> ((0 + 0) + 0) + 0) at_top"
      by (rule tendsto_add[OF second uu_decay])
    show ?thesis using third by simp
  qed
  have eventual_expansion:
      "\<forall>\<^sub>F frequency in at_top.
        ?full frequency =
          ?tt frequency + ?lc frequency + ?rc frequency + ?uu frequency"
    by (rule always_eventually) (rule allI, rule expansion)
  from sum_decay show ?thesis
    by (rule tendsto_cong[OF eventual_expansion, THEN iffD2])
qed

end

end
