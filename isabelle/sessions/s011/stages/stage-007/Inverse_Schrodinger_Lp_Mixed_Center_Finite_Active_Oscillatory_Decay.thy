theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Active_Oscillatory_Decay
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_007.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Active_Quadratic_Form"
begin

hide_const (open) Commutative_Ring.norm

section \<open>A.e. decay of the active mixed oscillatory fiber\<close>

context aim_planar_riesz_hls
begin

theorem slp_mixed_center_finite_active_oscillatory_fiber_decay:
  fixes B C p :: real
    and active_type ::
      "((unit + ((('i::finite + 'i) + unit) + ('j::finite + 'j)))
        \<times> bool) itself"
    and cutoff left_potential right_potential root_weight ::
      "slp_point \<Rightarrow> complex"
  assumes stationary_phase:
      "hormander_quadratic_stationary_phase_decay_claim active_type"
    and density:
      "evans_compact_smooth_l1_density_claim active_type"
    and B_nonnegative: "0 \<le> B"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and left_potential_lp: "aim_complex_lp_on_plane p left_potential"
    and right_potential_lp: "aim_complex_lp_on_plane p right_potential"
    and cutoff_bound: "\<And>x. norm (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
    and root_weight_integrable: "integrable lborel root_weight"
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
          (slp_mixed_center_finite_active_oscillatory_integrand frequency
            root_weight cutoff left_potential cutoff right_potential center ::
            real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool)
              \<Rightarrow> complex))
        \<longlongrightarrow> 0) at_top"
proof -
  have amplitude_integrable:
      "AE center in lborel.
        integrable lborel
          (slp_mixed_center_finite_active_complex_amplitude root_weight cutoff
            left_potential cutoff right_potential center ::
            real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool)
              \<Rightarrow> complex)"
    by (rule
          slp_mixed_center_finite_active_complex_amplitude_fiber_integrable[OF
            B_nonnegative p_lower p_upper cutoff_measurable left_potential_lp
            right_potential_lp cutoff_bound C_nonnegative
            root_weight_integrable root_support cutoff_support
            left_potential_support right_potential_support])
  show ?thesis
    using amplitude_integrable
  proof eventually_elim
    fix center
    assume amplitude:
      "integrable lborel
        (slp_mixed_center_finite_active_complex_amplitude root_weight cutoff
          left_potential cutoff right_potential center ::
          real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool)
            \<Rightarrow> complex)"
    show
      "((\<lambda>frequency.
        integral\<^sup>L lborel
          (slp_mixed_center_finite_active_oscillatory_integrand frequency
            root_weight cutoff left_potential cutoff right_potential center ::
            real^((unit + ((('i + 'i) + unit) + ('j + 'j))) \<times> bool)
              \<Rightarrow> complex))
        \<longlongrightarrow> 0) at_top"
      unfolding slp_mixed_center_finite_active_oscillatory_integrand_def
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

end

end
