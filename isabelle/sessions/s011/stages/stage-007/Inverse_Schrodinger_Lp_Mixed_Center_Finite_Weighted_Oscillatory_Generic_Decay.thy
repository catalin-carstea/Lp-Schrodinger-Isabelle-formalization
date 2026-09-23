theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Oscillatory_Generic_Decay
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_007.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Oscillatory_Cauchy_Integrable"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_007.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Active_Quadratic_Form"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Generic weighted oscillatory fiber decay\<close>

theorem slp_mixed_center_finite_weighted_active_oscillatory_decay:
  fixes active_type ::
      "((unit + (((('i::finite) + 'i) + unit) + (('j::finite) + 'j)))
        \<times> bool) itself"
    and root_weight left_cutoff left_potential left_terminal_value
      right_cutoff right_potential right_terminal_value center_factor ::
      slp_scalar_field
  assumes stationary_phase:
      "hormander_quadratic_stationary_phase_decay_claim active_type"
    and density:
      "evans_compact_smooth_l1_density_claim active_type"
    and root_weight_measurable:
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
          (slp_mixed_center_finite_weighted_active_complex_amplitude
            root_weight left_cutoff left_potential left_terminal_value
            right_cutoff right_potential right_terminal_value center_factor
            center ::
            real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool)
              \<Rightarrow> complex)"
  shows
    "AE center in lborel.
      ((\<lambda>frequency.
        integral\<^sup>L lborel
          (slp_mixed_center_finite_weighted_active_oscillatory_integrand
            frequency root_weight left_cutoff left_potential
            left_terminal_value right_cutoff right_potential
            right_terminal_value center_factor center ::
            real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool)
              \<Rightarrow> complex))
        \<longlongrightarrow> 0) at_top"
  using amplitude_integrable
proof eventually_elim
  fix center
  assume amplitude:
    "integrable lborel
      (slp_mixed_center_finite_weighted_active_complex_amplitude root_weight
        left_cutoff left_potential left_terminal_value right_cutoff
        right_potential right_terminal_value center_factor center ::
        real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool)
          \<Rightarrow> complex)"
  show
    "((\<lambda>frequency.
      integral\<^sup>L lborel
        (slp_mixed_center_finite_weighted_active_oscillatory_integrand
          frequency root_weight left_cutoff left_potential
          left_terminal_value right_cutoff right_potential
          right_terminal_value center_factor center ::
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

theorem slp_mixed_center_finite_weighted_oscillatory_fiber_decay:
  fixes active_type ::
      "((unit + (((('i::finite) + 'i) + unit) + (('j::finite) + 'j)))
        \<times> bool) itself"
    and root_weight left_cutoff left_potential left_terminal_value
      right_cutoff right_potential right_terminal_value center_factor ::
      slp_scalar_field
  assumes stationary_phase:
      "hormander_quadratic_stationary_phase_decay_claim active_type"
    and density:
      "evans_compact_smooth_l1_density_claim active_type"
    and root_weight_measurable:
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
          (slp_mixed_center_finite_weighted_active_complex_amplitude
            root_weight left_cutoff left_potential left_terminal_value
            right_cutoff right_potential right_terminal_value center_factor
            center ::
            real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool)
              \<Rightarrow> complex)"
  shows
    "AE center in lborel.
      ((\<lambda>frequency.
        integral\<^sup>L lborel
          (slp_mixed_center_finite_weighted_oscillatory_integrand frequency
            root_weight left_cutoff left_potential left_terminal_value
            right_cutoff right_potential right_terminal_value center_factor
            center ::
            ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex))
        \<longlongrightarrow> 0) at_top"
proof -
  have active_decay:
      "AE center in lborel.
        ((\<lambda>frequency.
          integral\<^sup>L lborel
            (slp_mixed_center_finite_weighted_active_oscillatory_integrand
              frequency root_weight left_cutoff left_potential
              left_terminal_value right_cutoff right_potential
              right_terminal_value center_factor center ::
              real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool)
                \<Rightarrow> complex))
          \<longlongrightarrow> 0) at_top"
    by (rule slp_mixed_center_finite_weighted_active_oscillatory_decay[OF
          stationary_phase density root_weight_measurable
          left_cutoff_measurable left_potential_measurable
          left_terminal_measurable right_cutoff_measurable
          right_potential_measurable right_terminal_measurable
          center_factor_measurable amplitude_integrable])
  show ?thesis
    using active_decay
  proof eventually_elim
    fix center
    assume decay:
      "((\<lambda>frequency.
        integral\<^sup>L lborel
          (slp_mixed_center_finite_weighted_active_oscillatory_integrand
            frequency root_weight left_cutoff left_potential
            left_terminal_value right_cutoff right_potential
            right_terminal_value center_factor center ::
            real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool)
              \<Rightarrow> complex))
        \<longlongrightarrow> 0) at_top"
    have transport:
      "(\<lambda>frequency.
        integral\<^sup>L lborel
          (slp_mixed_center_finite_weighted_active_oscillatory_integrand
            frequency root_weight left_cutoff left_potential
            left_terminal_value right_cutoff right_potential
            right_terminal_value center_factor center ::
            real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool)
              \<Rightarrow> complex)) =
       (\<lambda>frequency.
        integral\<^sup>L lborel
          (slp_mixed_center_finite_weighted_oscillatory_integrand frequency
            root_weight left_cutoff left_potential left_terminal_value
            right_cutoff right_potential right_terminal_value center_factor
            center ::
            ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex))"
    proof (rule ext)
      fix frequency
      have active_measurable:
          "(slp_mixed_center_finite_weighted_active_oscillatory_integrand
              frequency root_weight left_cutoff left_potential
              left_terminal_value right_cutoff right_potential
              right_terminal_value center_factor center ::
            real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool)
              \<Rightarrow> complex) \<in> borel_measurable lborel"
        by (rule
          slp_mixed_center_finite_weighted_active_oscillatory_integrand_measurable[OF
            root_weight_measurable left_cutoff_measurable
            left_potential_measurable left_terminal_measurable
            right_cutoff_measurable right_potential_measurable
            right_terminal_measurable center_factor_measurable])
      show
        "integral\<^sup>L lborel
            (slp_mixed_center_finite_weighted_active_oscillatory_integrand
              frequency root_weight left_cutoff left_potential
              left_terminal_value right_cutoff right_potential
              right_terminal_value center_factor center ::
              real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool)
                \<Rightarrow> complex) =
          integral\<^sup>L lborel
            (slp_mixed_center_finite_weighted_oscillatory_integrand frequency
              root_weight left_cutoff left_potential left_terminal_value
              right_cutoff right_potential right_terminal_value center_factor
              center ::
              ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex)"
        using slp_mixed_center_finite_active_integral[OF active_measurable]
        by (simp only:
          slp_mixed_center_finite_weighted_active_oscillatory_integrand_pack)
    qed
    show
      "((\<lambda>frequency.
        integral\<^sup>L lborel
          (slp_mixed_center_finite_weighted_oscillatory_integrand frequency
            root_weight left_cutoff left_potential left_terminal_value
            right_cutoff right_potential right_terminal_value center_factor
            center ::
            ('i, 'j) slp_mixed_center_finite_coordinates \<Rightarrow> complex))
        \<longlongrightarrow> 0) at_top"
      using decay by (simp only: transport)
  qed
qed

end
