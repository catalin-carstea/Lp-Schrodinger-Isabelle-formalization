theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Oscillatory_Kernel_Decay
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_007.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Oscillatory_Fiber_Decay"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_006.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Oscillatory_Kernel"
begin

hide_const (open) Commutative_Ring.norm

section \<open>A.e. decay of the exact mixed center kernel\<close>

context aim_planar_riesz_hls
begin

theorem slp_mixed_center_finite_oscillatory_kernel_decay:
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
        slp_mixed_center_finite_oscillatory_kernel TYPE('i) TYPE('j)
          frequency root_weight cutoff left_potential cutoff right_potential
          center)
        \<longlongrightarrow> 0) at_top"
  using slp_mixed_center_finite_oscillatory_fiber_decay[OF
      stationary_phase density B_nonnegative p_lower p_upper
      cutoff_measurable left_potential_lp right_potential_lp cutoff_bound
      C_nonnegative root_weight_integrable root_support cutoff_support
      left_potential_support right_potential_support]
  unfolding slp_mixed_center_finite_oscillatory_kernel_def
    slp_mixed_center_finite_fiber_integral_def
    slp_parameterized_real_phase_fiber_integral_def
    slp_parameterized_complex_fiber_integral_def
    slp_mixed_center_finite_oscillatory_integrand_def .

end

end
