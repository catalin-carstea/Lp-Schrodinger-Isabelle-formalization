theory Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Unit_Kernel_Factorization
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_007.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Weighted_Oscillatory_Cauchy_Kernel"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_006.Inverse_Schrodinger_Lp_Mixed_Center_Finite_Oscillatory_Kernel"
begin

section \<open>Unit-terminal weighted kernel factorization\<close>

theorem slp_mixed_center_finite_weighted_oscillatory_kernel_unit_factorization:
  "slp_mixed_center_finite_weighted_oscillatory_kernel
      TYPE('i::finite) TYPE('j::finite) frequency root_weight left_cutoff
      left_potential (\<lambda>_. 1) right_cutoff right_potential (\<lambda>_. 1)
      center_factor center =
    slp_mixed_center_finite_oscillatory_kernel TYPE('i) TYPE('j) frequency
      root_weight left_cutoff left_potential right_cutoff right_potential
      center * center_factor center"
  unfolding slp_mixed_center_finite_weighted_oscillatory_kernel_def
    slp_mixed_center_finite_weighted_oscillatory_integrand_def
    slp_mixed_center_finite_weighted_complex_amplitude_def
    slp_mixed_center_finite_oscillatory_kernel_def
    slp_mixed_center_finite_fiber_integral_def
    slp_parameterized_real_phase_fiber_integral_def
    slp_parameterized_complex_fiber_integral_def
    slp_parameterized_real_phase_integrand_def
    slp_mixed_center_finite_complex_amplitude_def
  by (simp add: algebra_simps
      Bochner_Integration.integral_mult_left_zero)

end
