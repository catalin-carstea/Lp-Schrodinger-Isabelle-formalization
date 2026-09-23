theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Oscillatory_Cauchy_Decay
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_007.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Oscillatory_Cauchy_Integrable"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_007.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Active_Quadratic_Form"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Actual-terminal weighted oscillatory fiber decay\<close>

context aim_planar_riesz_hls_cauchy
begin

theorem slp_mixed_center_finite_weighted_active_oscillatory_cauchy_decay:
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
    "AE center in lborel.
      ((\<lambda>frequency.
        integral\<^sup>L lborel
          (slp_mixed_center_finite_weighted_active_oscillatory_integrand
            frequency root_weight cutoff left_potential
            (slp_cauchy_transform left_orientation left_potential) cutoff
            right_potential
            (slp_cauchy_transform right_orientation right_potential)
            center_factor center ::
            real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool)
              \<Rightarrow> complex))
        \<longlongrightarrow> 0) at_top"
proof -
  let ?left_terminal =
    "slp_cauchy_transform left_orientation left_potential"
  let ?right_terminal =
    "slp_cauchy_transform right_orientation right_potential"
  have amplitude_integrable:
      "AE center in lborel.
        integrable lborel
          (slp_mixed_center_finite_weighted_active_complex_amplitude
            root_weight cutoff left_potential ?left_terminal cutoff
            right_potential ?right_terminal center_factor center ::
            real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool)
              \<Rightarrow> complex)"
    by (rule
      slp_mixed_center_finite_weighted_active_amplitude_cauchy_integrable[OF
        B_nonnegative C_nonnegative p_lower p_upper X_measurable X_bounded
        cutoff_measurable center_factor_measurable left_potential_lp
        right_potential_lp root_weight_lp root_weight_outside cutoff_bound
        center_factor_bound root_support cutoff_support left_potential_support
        right_potential_support])
  show ?thesis
    using amplitude_integrable
  proof eventually_elim
    fix center
    assume amplitude:
      "integrable lborel
        (slp_mixed_center_finite_weighted_active_complex_amplitude root_weight
          cutoff left_potential ?left_terminal cutoff right_potential
          ?right_terminal center_factor center ::
          real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool)
            \<Rightarrow> complex)"
    show
      "((\<lambda>frequency.
        integral\<^sup>L lborel
          (slp_mixed_center_finite_weighted_active_oscillatory_integrand
            frequency root_weight cutoff left_potential ?left_terminal cutoff
            right_potential ?right_terminal center_factor center ::
            real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool)
              \<Rightarrow> complex))
        \<longlongrightarrow> 0) at_top"
      unfolding
        slp_mixed_center_finite_weighted_active_oscillatory_integrand_def
        slp_parameterized_real_phase_integrand_def
      apply (simp only:
        slp_mixed_center_finite_active_residual_quadratic_form)
      apply (rule
        hormander_quadratic_stationary_phase_decay.slp_quadratic_decay_affine)
      subgoal
        using stationary_phase
        unfolding hormander_quadratic_stationary_phase_decay_def
          hormander_quadratic_stationary_phase_decay_claim_def
        by assumption
      subgoal
        using density
        unfolding evans_compact_smooth_l1_density_claim_def
        by assumption
      subgoal by (rule slp_mixed_center_finite_active_hessian_symmetric)
      subgoal by (rule slp_mixed_center_finite_active_hessian_nondegenerate)
      subgoal by (rule amplitude)
      done
  qed
qed

theorem slp_mixed_center_finite_weighted_oscillatory_cauchy_fiber_decay:
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
    "AE center in lborel.
      ((\<lambda>frequency.
        integral\<^sup>L lborel
          (slp_mixed_center_finite_weighted_oscillatory_integrand frequency
            root_weight cutoff left_potential
            (slp_cauchy_transform left_orientation left_potential) cutoff
            right_potential
            (slp_cauchy_transform right_orientation right_potential)
            center_factor center ::
            ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex))
        \<longlongrightarrow> 0) at_top"
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
  have active_decay:
      "AE center in lborel.
        ((\<lambda>frequency.
          integral\<^sup>L lborel
            (slp_mixed_center_finite_weighted_active_oscillatory_integrand
              frequency root_weight cutoff left_potential ?left_terminal
              cutoff right_potential ?right_terminal center_factor center ::
              real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool)
                \<Rightarrow> complex))
          \<longlongrightarrow> 0) at_top"
    by (rule
      slp_mixed_center_finite_weighted_active_oscillatory_cauchy_decay[OF
        stationary_phase density B_nonnegative C_nonnegative p_lower p_upper
        X_measurable X_bounded cutoff_measurable center_factor_measurable
        left_potential_lp right_potential_lp root_weight_lp
        root_weight_outside cutoff_bound center_factor_bound root_support
        cutoff_support left_potential_support right_potential_support])
  show ?thesis
    using active_decay
  proof eventually_elim
    fix center
    assume decay:
      "((\<lambda>frequency.
        integral\<^sup>L lborel
          (slp_mixed_center_finite_weighted_active_oscillatory_integrand
            frequency root_weight cutoff left_potential ?left_terminal cutoff
            right_potential ?right_terminal center_factor center ::
            real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool)
              \<Rightarrow> complex))
        \<longlongrightarrow> 0) at_top"
    have transport:
      "(\<lambda>frequency.
        integral\<^sup>L lborel
          (slp_mixed_center_finite_weighted_active_oscillatory_integrand
            frequency root_weight cutoff left_potential ?left_terminal cutoff
            right_potential ?right_terminal center_factor center ::
            real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool)
              \<Rightarrow> complex)) =
       (\<lambda>frequency.
        integral\<^sup>L lborel
          (slp_mixed_center_finite_weighted_oscillatory_integrand frequency
            root_weight cutoff left_potential ?left_terminal cutoff
            right_potential ?right_terminal center_factor center ::
            ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex))"
    proof (rule ext)
      fix frequency
      have active_measurable:
          "(slp_mixed_center_finite_weighted_active_oscillatory_integrand
              frequency root_weight cutoff left_potential ?left_terminal
              cutoff right_potential ?right_terminal center_factor center ::
            real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool)
              \<Rightarrow> complex) \<in> borel_measurable lborel"
        by (rule
          slp_mixed_center_finite_weighted_active_oscillatory_integrand_measurable[OF
            root_weight_measurable cutoff_measurable
            left_potential_measurable left_terminal_measurable
            cutoff_measurable right_potential_measurable
            right_terminal_measurable center_factor_measurable])
      show
        "integral\<^sup>L lborel
            (slp_mixed_center_finite_weighted_active_oscillatory_integrand
              frequency root_weight cutoff left_potential ?left_terminal
              cutoff right_potential ?right_terminal center_factor center ::
              real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool)
                \<Rightarrow> complex) =
          integral\<^sup>L lborel
            (slp_mixed_center_finite_weighted_oscillatory_integrand frequency
              root_weight cutoff left_potential ?left_terminal cutoff
              right_potential ?right_terminal center_factor center ::
              ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
        using slp_mixed_center_finite_active_integral[OF active_measurable]
        by (simp only:
          slp_mixed_center_finite_weighted_active_oscillatory_integrand_pack)
    qed
    show
      "((\<lambda>frequency.
        integral\<^sup>L lborel
          (slp_mixed_center_finite_weighted_oscillatory_integrand frequency
            root_weight cutoff left_potential ?left_terminal cutoff
            right_potential ?right_terminal center_factor center ::
            ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex))
        \<longlongrightarrow> 0) at_top"
      using decay by (simp only: transport)
  qed
qed

end

end
