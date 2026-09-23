theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Oscillatory_Cauchy_Global_Decay
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_007.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Oscillatory_Cauchy_Kernel"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_007.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Oscillatory_Cauchy_Decay"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Actual-terminal weighted decay after center integration\<close>

context aim_planar_riesz_hls_cauchy
begin

theorem slp_mixed_center_finite_weighted_oscillatory_cauchy_global_decay:
  fixes B C D p :: real
    and active_type ::
      "((unit + ((('i::finite + 'i) + unit) + ('j::finite + 'j)))
        \<times> bool) itself"
    and X :: "slp_point set"
    and root_weight cutoff left_potential right_potential center_factor ::
      slp_scalar_field
    and left_orientation right_orientation :: slp_cauchy_orientation
  assumes stationary_phase:
      "hormander_quadratic_stationary_phase_decay_claim active_type"
    and density:
      "evans_compact_smooth_l1_density_claim active_type"
    and B_nonnegative: "0 \<le> B"
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
    "((\<lambda>frequency.
      integral\<^sup>L lborel
        (slp_mixed_center_finite_weighted_oscillatory_kernel
          TYPE('i) TYPE('j) frequency root_weight cutoff left_potential
          (slp_cauchy_transform left_orientation left_potential) cutoff
          right_potential
          (slp_cauchy_transform right_orientation right_potential)
          center_factor))
      \<longlongrightarrow> 0) at_top"
proof -
  let ?left_terminal =
    "slp_cauchy_transform left_orientation left_potential"
  let ?right_terminal =
    "slp_cauchy_transform right_orientation right_potential"
  let ?mass =
    "slp_mixed_center_finite_weighted_absolute_fiber_mass
      TYPE('i) TYPE('j) root_weight cutoff left_potential ?left_terminal
      cutoff right_potential ?right_terminal center_factor"
  let ?majorant = "\<lambda>center. enn2real (?mass center)"
  let ?kernel = "\<lambda>frequency.
    slp_mixed_center_finite_weighted_oscillatory_kernel
      TYPE('i) TYPE('j) frequency root_weight cutoff left_potential
      ?left_terminal cutoff right_potential ?right_terminal center_factor"
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
  have mass_measurable:
      "?mass \<in> borel_measurable lborel"
    by (rule
      slp_mixed_center_finite_weighted_absolute_fiber_mass_measurable[OF
        root_weight_measurable cutoff_measurable left_potential_measurable
        left_terminal_measurable cutoff_measurable right_potential_measurable
        right_terminal_measurable center_factor_measurable])
  have mass_integral_finite:
      "nn_integral lborel ?mass < top_class.top"
    by (rule
      slp_mixed_center_finite_weighted_absolute_mass_cauchy_finite[OF
        B_nonnegative C_nonnegative p_lower p_upper X_measurable X_bounded
        cutoff_measurable left_potential_lp right_potential_lp root_weight_lp
        root_weight_outside cutoff_bound center_factor_bound root_support
        cutoff_support left_potential_support right_potential_support])
  have mass_finite:
      "AE center in lborel. ?mass center < top_class.top"
  proof -
    have integral_not_infinity: "nn_integral lborel ?mass \<noteq> \<infinity>"
      using mass_integral_finite by simp
    have raw_ae: "AE center in lborel. ?mass center \<noteq> \<infinity>"
      by (rule nn_integral_PInf_AE[OF mass_measurable
            integral_not_infinity])
    show ?thesis
      using raw_ae by (simp add: less_top)
  qed
  have majorant_measurable:
      "?majorant \<in> borel_measurable lborel"
    using mass_measurable by measurable
  have majorant_nn_integral:
      "nn_integral lborel ?majorant = nn_integral lborel ?mass"
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
  have kernel_measurable:
      "\<And>frequency. ?kernel frequency \<in> borel_measurable lborel"
    by (rule
      slp_mixed_center_finite_weighted_oscillatory_cauchy_kernel_properties(1)[OF
        B_nonnegative C_nonnegative p_lower p_upper X_measurable X_bounded
        cutoff_measurable center_factor_measurable left_potential_lp
        right_potential_lp root_weight_lp root_weight_outside cutoff_bound
        center_factor_bound root_support cutoff_support left_potential_support
        right_potential_support])
  have kernel_bound_ennreal:
      "\<And>frequency. AE center in lborel.
        ennreal (norm_class.norm (?kernel frequency center)) \<le> ?mass center"
    by (rule
      slp_mixed_center_finite_weighted_oscillatory_cauchy_kernel_properties(2)[OF
        B_nonnegative C_nonnegative p_lower p_upper X_measurable X_bounded
        cutoff_measurable center_factor_measurable left_potential_lp
        right_potential_lp root_weight_lp root_weight_outside cutoff_bound
        center_factor_bound root_support cutoff_support left_potential_support
        right_potential_support])
  have kernel_bound_real:
      "\<And>frequency. AE center in lborel.
        norm_class.norm (?kernel frequency center) \<le> ?majorant center"
  proof -
    fix frequency
    show
      "AE center in lborel.
        norm_class.norm (?kernel frequency center) \<le> ?majorant center"
      using kernel_bound_ennreal[of frequency] mass_finite
    proof eventually_elim
      fix center
      assume bound:
          "ennreal (norm_class.norm (?kernel frequency center)) \<le>
            ?mass center"
        and finite: "?mass center < top_class.top"
      have
        "enn2real (ennreal (norm_class.norm (?kernel frequency center))) \<le>
          enn2real (?mass center)"
        by (rule enn2real_mono[OF bound finite])
      then show
        "norm_class.norm (?kernel frequency center) \<le> ?majorant center"
        by simp
    qed
  qed
  have pointwise_decay:
      "AE center in lborel.
        ((\<lambda>frequency. ?kernel frequency center) \<longlongrightarrow> 0)
          at_top"
    unfolding slp_mixed_center_finite_weighted_oscillatory_kernel_def
    by (rule
      slp_mixed_center_finite_weighted_oscillatory_cauchy_fiber_decay[OF
        stationary_phase density B_nonnegative C_nonnegative p_lower p_upper
        X_measurable X_bounded cutoff_measurable center_factor_measurable
        left_potential_lp right_potential_lp root_weight_lp
        root_weight_outside cutoff_bound center_factor_bound root_support
        cutoff_support left_potential_support right_potential_support])
  have eventually_bound:
      "\<forall>\<^sub>F frequency in at_top.
        AE center in lborel.
          norm_class.norm (?kernel frequency center) \<le> ?majorant center"
    by (rule always_eventually) (intro allI, rule kernel_bound_real)
  have zero_measurable:
      "(\<lambda>_ :: slp_point. (0 :: complex)) \<in> borel_measurable lborel"
    by measurable
  have global_decay:
      "((\<lambda>frequency. integral\<^sup>L lborel (?kernel frequency))
        \<longlongrightarrow>
        integral\<^sup>L lborel (\<lambda>_ :: slp_point. (0 :: complex)))
        at_top"
    by (rule integral_dominated_convergence_at_top[OF zero_measurable
          kernel_measurable majorant_integrable pointwise_decay
          eventually_bound])
  show ?thesis
    using global_decay by simp
qed

end

end
