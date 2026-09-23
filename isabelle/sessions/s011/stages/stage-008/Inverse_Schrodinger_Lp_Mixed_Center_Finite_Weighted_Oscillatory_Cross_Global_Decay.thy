theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Oscillatory_Cross_Global_Decay
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_007.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Oscillatory_Cross_Decay"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Center dominated convergence from an ennreal mass\<close>

theorem slp_ennreal_mass_dominated_center_integral_decay:
  fixes mass :: "slp_point \<Rightarrow> ennreal"
    and kernel :: "real \<Rightarrow> slp_point \<Rightarrow> complex"
  assumes mass_measurable: "mass \<in> borel_measurable lborel"
    and mass_integral_finite:
      "nn_integral lborel mass < top_class.top"
    and kernel_measurable:
      "\<And>frequency. kernel frequency \<in> borel_measurable lborel"
    and kernel_bound:
      "\<And>frequency. AE center in lborel.
        ennreal (norm_class.norm (kernel frequency center)) \<le> mass center"
    and pointwise_decay:
      "AE center in lborel.
        ((\<lambda>frequency. kernel frequency center) \<longlongrightarrow> 0) at_top"
  shows
    "((\<lambda>frequency. integral\<^sup>L lborel (kernel frequency))
      \<longlongrightarrow> 0) at_top"
proof -
  let ?majorant = "\<lambda>center. enn2real (mass center)"
  have mass_finite:
      "AE center in lborel. mass center < top_class.top"
  proof -
    have integral_not_infinity: "nn_integral lborel mass \<noteq> \<infinity>"
      using mass_integral_finite by simp
    have raw_ae: "AE center in lborel. mass center \<noteq> \<infinity>"
      by (rule nn_integral_PInf_AE[OF mass_measurable
            integral_not_infinity])
    show ?thesis
      using raw_ae by (simp add: less_top)
  qed
  have majorant_measurable:
      "?majorant \<in> borel_measurable lborel"
    using mass_measurable by measurable
  have majorant_nn_integral:
      "nn_integral lborel ?majorant = nn_integral lborel mass"
    by (rule nn_integral_cong_AE)
      (use mass_finite in \<open>eventually_elim, simp\<close>)
  have majorant_integrable:
      "integrable lborel ?majorant"
  proof (rule integrableI_nonneg)
    show "?majorant \<in> borel_measurable lborel"
      by (rule majorant_measurable)
    show "AE center in lborel. 0 \<le> ?majorant center"
      by simp
    show "nn_integral lborel ?majorant < \<infinity>"
      using majorant_nn_integral mass_integral_finite by simp
  qed
  have kernel_bound_real:
      "\<And>frequency. AE center in lborel.
        norm_class.norm (kernel frequency center) \<le> ?majorant center"
  proof -
    fix frequency
    show
      "AE center in lborel.
        norm_class.norm (kernel frequency center) \<le> ?majorant center"
      using kernel_bound[of frequency] mass_finite
    proof eventually_elim
      fix center
      assume bound:
          "ennreal (norm_class.norm (kernel frequency center)) \<le> mass center"
        and finite: "mass center < top_class.top"
      have
        "enn2real (ennreal (norm_class.norm (kernel frequency center))) \<le>
          enn2real (mass center)"
        by (rule enn2real_mono[OF bound finite])
      then show
        "norm_class.norm (kernel frequency center) \<le> ?majorant center"
        by simp
    qed
  qed
  have eventually_bound:
      "\<forall>\<^sub>F frequency in at_top.
        AE center in lborel.
          norm_class.norm (kernel frequency center) \<le> ?majorant center"
    by (rule always_eventually) (intro allI, rule kernel_bound_real)
  have zero_measurable:
      "(\<lambda>_ :: slp_point. (0 :: complex)) \<in> borel_measurable lborel"
    by measurable
  have global_decay:
      "((\<lambda>frequency. integral\<^sup>L lborel (kernel frequency))
        \<longlongrightarrow>
        integral\<^sup>L lborel (\<lambda>_ :: slp_point. (0 :: complex)))
        at_top"
    by (rule integral_dominated_convergence_at_top[OF zero_measurable
          kernel_measurable majorant_integrable pointwise_decay
          eventually_bound])
  show ?thesis
    using global_decay by simp
qed

context aim_planar_riesz_hls_cauchy
begin

theorem slp_mixed_center_finite_weighted_oscillatory_cross_global_decay:
  fixes active_type ::
      "((unit + (((('i::finite) + 'i) + unit) + (('j::finite) + 'j)))
        \<times> bool) itself"
    and B C p :: real
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
  shows left:
    "((\<lambda>frequency.
      integral\<^sup>L lborel
        (slp_mixed_center_finite_weighted_oscillatory_kernel
          TYPE('i) TYPE('j) frequency root_weight cutoff left_potential
          (slp_cauchy_transform left_orientation left_potential) cutoff
          right_potential (\<lambda>_. 1)
          (\<lambda>x. -(phi x *
            slp_cauchy_transform right_orientation right_potential x))))
      \<longlongrightarrow> 0) at_top"
    and right:
    "((\<lambda>frequency.
      integral\<^sup>L lborel
        (slp_mixed_center_finite_weighted_oscillatory_kernel
          TYPE('i) TYPE('j) frequency root_weight cutoff left_potential
          (\<lambda>_. 1) cutoff right_potential
          (slp_cauchy_transform right_orientation right_potential)
          (\<lambda>x. -(phi x *
            slp_cauchy_transform left_orientation left_potential x))))
      \<longlongrightarrow> 0) at_top"
proof -
  let ?left_terminal =
    "slp_cauchy_transform left_orientation left_potential"
  let ?right_terminal =
    "slp_cauchy_transform right_orientation right_potential"
  let ?left_center = "\<lambda>x. -(phi x * ?right_terminal x)"
  let ?right_center = "\<lambda>x. -(phi x * ?left_terminal x)"
  let ?left_mass =
    "slp_mixed_center_finite_weighted_absolute_fiber_mass
      TYPE('i) TYPE('j) root_weight cutoff left_potential ?left_terminal
      cutoff right_potential (\<lambda>_. 1) ?left_center"
  let ?right_mass =
    "slp_mixed_center_finite_weighted_absolute_fiber_mass
      TYPE('i) TYPE('j) root_weight cutoff left_potential (\<lambda>_. 1)
      cutoff right_potential ?right_terminal ?right_center"
  let ?left_kernel = "\<lambda>frequency.
    slp_mixed_center_finite_weighted_oscillatory_kernel
      TYPE('i) TYPE('j) frequency root_weight cutoff left_potential
      ?left_terminal cutoff right_potential (\<lambda>_. 1) ?left_center"
  let ?right_kernel = "\<lambda>frequency.
    slp_mixed_center_finite_weighted_oscillatory_kernel
      TYPE('i) TYPE('j) frequency root_weight cutoff left_potential
      (\<lambda>_. 1) cutoff right_potential ?right_terminal ?right_center"
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
  have unit_measurable:
      "(\<lambda>_ :: slp_point. (1 :: complex)) \<in> borel_measurable lborel"
    by measurable
  have left_center_measurable:
      "?left_center \<in> borel_measurable lborel"
    using phi_measurable right_terminal_measurable by measurable
  have right_center_measurable:
      "?right_center \<in> borel_measurable lborel"
    using phi_measurable left_terminal_measurable by measurable
  have left_mass_measurable:
      "?left_mass \<in> borel_measurable lborel"
    by (rule
      slp_mixed_center_finite_weighted_absolute_fiber_mass_measurable[OF
        root_weight_measurable cutoff_measurable left_potential_measurable
        left_terminal_measurable cutoff_measurable right_potential_measurable
        unit_measurable left_center_measurable])
  have right_mass_measurable:
      "?right_mass \<in> borel_measurable lborel"
    by (rule
      slp_mixed_center_finite_weighted_absolute_fiber_mass_measurable[OF
        root_weight_measurable cutoff_measurable left_potential_measurable
        unit_measurable cutoff_measurable right_potential_measurable
        right_terminal_measurable right_center_measurable])
  have left_mass_finite:
      "nn_integral lborel ?left_mass < top_class.top"
    by (rule
      slp_mixed_center_finite_weighted_absolute_mass_left_cross_finite[OF
        B_nonnegative C_nonnegative p_lower p_upper X_measurable X_bounded
        phi_test cutoff_measurable left_potential_lp right_potential_lp
        root_weight_lp root_weight_outside cutoff_bound root_support
        cutoff_support left_potential_support right_potential_support])
  have right_mass_finite:
      "nn_integral lborel ?right_mass < top_class.top"
    by (rule
      slp_mixed_center_finite_weighted_absolute_mass_right_cross_finite[OF
        B_nonnegative C_nonnegative p_lower p_upper X_measurable X_bounded
        phi_test cutoff_measurable left_potential_lp right_potential_lp
        root_weight_lp root_weight_outside cutoff_bound root_support
        cutoff_support left_potential_support right_potential_support])
  have left_amplitude_integrable:
      "AE center in lborel.
        integrable lborel
          (slp_mixed_center_finite_weighted_complex_amplitude root_weight
            cutoff left_potential ?left_terminal cutoff right_potential
            (\<lambda>_. 1) ?left_center center ::
            ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
    by (rule
      slp_mixed_center_finite_weighted_amplitude_fiber_integrable_from_mass[OF
        root_weight_measurable cutoff_measurable left_potential_measurable
        left_terminal_measurable cutoff_measurable right_potential_measurable
        unit_measurable left_center_measurable left_mass_finite])
  have right_amplitude_integrable:
      "AE center in lborel.
        integrable lborel
          (slp_mixed_center_finite_weighted_complex_amplitude root_weight
            cutoff left_potential (\<lambda>_. 1) cutoff right_potential
            ?right_terminal ?right_center center ::
            ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
    by (rule
      slp_mixed_center_finite_weighted_amplitude_fiber_integrable_from_mass[OF
        root_weight_measurable cutoff_measurable left_potential_measurable
        unit_measurable cutoff_measurable right_potential_measurable
        right_terminal_measurable right_center_measurable right_mass_finite])
  have left_kernel_measurable:
      "\<And>frequency. ?left_kernel frequency \<in> borel_measurable lborel"
    by (rule
      slp_mixed_center_finite_weighted_oscillatory_kernel_properties(1)[OF
        root_weight_measurable cutoff_measurable left_potential_measurable
        left_terminal_measurable cutoff_measurable right_potential_measurable
        unit_measurable left_center_measurable left_amplitude_integrable])
  have right_kernel_measurable:
      "\<And>frequency. ?right_kernel frequency \<in> borel_measurable lborel"
    by (rule
      slp_mixed_center_finite_weighted_oscillatory_kernel_properties(1)[OF
        root_weight_measurable cutoff_measurable left_potential_measurable
        unit_measurable cutoff_measurable right_potential_measurable
        right_terminal_measurable right_center_measurable
        right_amplitude_integrable])
  have left_kernel_bound:
      "\<And>frequency. AE center in lborel.
        ennreal (norm_class.norm (?left_kernel frequency center)) \<le>
          ?left_mass center"
    by (rule
      slp_mixed_center_finite_weighted_oscillatory_kernel_properties(2)[OF
        root_weight_measurable cutoff_measurable left_potential_measurable
        left_terminal_measurable cutoff_measurable right_potential_measurable
        unit_measurable left_center_measurable left_amplitude_integrable])
  have right_kernel_bound:
      "\<And>frequency. AE center in lborel.
        ennreal (norm_class.norm (?right_kernel frequency center)) \<le>
          ?right_mass center"
    by (rule
      slp_mixed_center_finite_weighted_oscillatory_kernel_properties(2)[OF
        root_weight_measurable cutoff_measurable left_potential_measurable
        unit_measurable cutoff_measurable right_potential_measurable
        right_terminal_measurable right_center_measurable
        right_amplitude_integrable])
  have left_pointwise_decay:
      "AE center in lborel.
        ((\<lambda>frequency. ?left_kernel frequency center)
          \<longlongrightarrow> 0) at_top"
    unfolding slp_mixed_center_finite_weighted_oscillatory_kernel_def
    by (rule
      slp_mixed_center_finite_weighted_oscillatory_cross_fiber_decay(1)[OF
        stationary_phase density B_nonnegative C_nonnegative p_lower p_upper
        X_measurable X_bounded phi_test cutoff_measurable left_potential_lp
        right_potential_lp root_weight_lp root_weight_outside cutoff_bound
        root_support cutoff_support left_potential_support
        right_potential_support])
  have right_pointwise_decay:
      "AE center in lborel.
        ((\<lambda>frequency. ?right_kernel frequency center)
          \<longlongrightarrow> 0) at_top"
    unfolding slp_mixed_center_finite_weighted_oscillatory_kernel_def
    by (rule
      slp_mixed_center_finite_weighted_oscillatory_cross_fiber_decay(2)[OF
        stationary_phase density B_nonnegative C_nonnegative p_lower p_upper
        X_measurable X_bounded phi_test cutoff_measurable left_potential_lp
        right_potential_lp root_weight_lp root_weight_outside cutoff_bound
        root_support cutoff_support left_potential_support
        right_potential_support])
  show
    "((\<lambda>frequency. integral\<^sup>L lborel (?left_kernel frequency))
      \<longlongrightarrow> 0) at_top"
    by (rule slp_ennreal_mass_dominated_center_integral_decay[OF
          left_mass_measurable left_mass_finite left_kernel_measurable
          left_kernel_bound left_pointwise_decay])
  show
    "((\<lambda>frequency. integral\<^sup>L lborel (?right_kernel frequency))
      \<longlongrightarrow> 0) at_top"
    by (rule slp_ennreal_mass_dominated_center_integral_decay[OF
          right_mass_measurable right_mass_finite right_kernel_measurable
          right_kernel_bound right_pointwise_decay])
qed

end

end
