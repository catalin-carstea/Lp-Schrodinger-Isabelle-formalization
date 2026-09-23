theory Inverse_Schrodinger_Lp_Physical_Subquadratic_Recovery
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_018.Inverse_Schrodinger_Lp_Compact_Smooth_Duality"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Physical almost-everywhere recovery below exponent two\<close>

context slp_cgo_full_weak_solution_context
begin

theorem slp_common_cgo_subquadratic_potential_ae_equal:
  fixes p epsilon A R A0 B0 B1 :: real
    and Omega X :: "slp_point set"
    and cutoff coefficient coefficient_tilde V V_tilde :: slp_scalar_field
  assumes stationary:
      "hormander_quadratic_stationary_phase_decay_claim TYPE(2)"
    and density: "evans_compact_smooth_l1_density_claim TYPE(2)"
    and fourier_plancherel:
      "hormander_euclidean_l2_fourier_plancherel_claim"
    and riesz_hls: "aim_planar_riesz_hls_claim"
    and cauchy_test_left_inverse:
      "aim_planar_cauchy_test_left_inverse_claim"
    and evans_density: "evans_compact_support_w1p_zero_density_claim"
    and compact_smooth_density:
      "evans_compact_smooth_lp_density_claim TYPE(2)"
    and exponent_lower: "1 < p"
    and exponent_upper: "p < 2"
    and loss_positive: "0 < epsilon"
    and loss_upper: "epsilon < 1 - 1 / p"
    and radius_nonnegative: "0 \<le> A"
    and radius_lower: "1 \<le> R"
    and set_radius:
      "\<And>y :: slp_point. y \<in> X \<Longrightarrow>
        Real_Vector_Spaces.norm y \<le> A"
    and center_geometry:
      "\<And>c y :: slp_point. c \<in> Omega \<Longrightarrow> y \<in> X \<Longrightarrow>
        Real_Vector_Spaces.norm (y - c) \<le> R"
    and X_open: "open X"
    and X_bounded: "bounded X"
    and Omega_subset: "Omega \<subseteq> X"
    and cutoff_test: "slp_test_function_on X cutoff"
    and cutoff_one: "\<And>z. z \<in> Omega \<Longrightarrow> cutoff z = 1"
    and cutoff_bound:
      "\<And>x. x \<in> X \<Longrightarrow>
        Real_Vector_Spaces.norm (cutoff x) \<le> A0"
    and cutoff_derivative_zero_bound:
      "\<And>x. x \<in> X \<Longrightarrow>
        Real_Vector_Spaces.norm
          (slp_complex_partial_derivative cutoff 0 x) \<le> B0"
    and cutoff_derivative_one_bound:
      "\<And>x. x \<in> X \<Longrightarrow>
        Real_Vector_Spaces.norm
          (slp_complex_partial_derivative cutoff 1 x) \<le> B1"
    and A0_nonnegative: "0 \<le> A0"
    and B0_nonnegative: "0 \<le> B0"
    and B1_nonnegative: "0 \<le> B1"
    and coefficient_lp: "aim_complex_lp_on_plane p coefficient"
    and coefficient_support:
      "{x. coefficient x \<noteq> 0} \<subseteq> Omega"
    and coefficient_tilde_lp:
      "aim_complex_lp_on_plane p coefficient_tilde"
    and coefficient_tilde_support:
      "{x. coefficient_tilde x \<noteq> 0} \<subseteq> Omega"
    and coefficient_normalization: "coefficient = (\<lambda>z. V z / 4)"
    and coefficient_tilde_normalization:
      "coefficient_tilde = (\<lambda>z. V_tilde z / 4)"
    and domain: "slp_bounded_smooth_domain Omega"
    and orthogonality:
      "slp_alessandrini_orthogonality Omega V V_tilde"
  shows "slp_potential_ae_equal Omega V V_tilde"
proof -
  let ?Q = "slp_restrict_field Omega (\<lambda>x. V x - V_tilde x)"
  have Omega_measurable: "Omega \<in> sets lborel"
    using slp_bounded_smooth_domain_lborel_carrier[OF domain] by blast
  have Omega_open: "open Omega"
    using domain unfolding slp_bounded_smooth_domain_def by blast
  have Omega_bounded: "bounded Omega"
    using domain unfolding slp_bounded_smooth_domain_def by blast
  have exponent_one_le: "1 \<le> p"
    using exponent_lower by linarith
  have exponent_positive: "0 < p"
    using exponent_lower by linarith
  have coefficient_difference_lp:
      "aim_complex_lp_on_plane p
        (\<lambda>x. coefficient x - coefficient_tilde x)"
    by (rule slp_complex_lp_diff_norm_coarse_triangle(1)[OF exponent_one_le
          coefficient_lp coefficient_tilde_lp])
  have four_measurable:
      "(\<lambda>_::slp_point. (4::complex)) \<in> borel_measurable lborel"
    by measurable
  have scaled_difference_lp:
      "aim_complex_lp_on_plane p
        (\<lambda>x. (4::complex) * (coefficient x - coefficient_tilde x))"
    by (rule slp_complex_lp_bounded_multiplier(1)[where C=4,
          OF exponent_positive four_measurable _ _ coefficient_difference_lp])
      simp_all
  have potential_difference_eq:
      "(\<lambda>x. V x - V_tilde x) =
        (\<lambda>x. (4::complex) * (coefficient x - coefficient_tilde x))"
  proof (rule ext)
    fix x
    show "V x - V_tilde x =
        (4::complex) * (coefficient x - coefficient_tilde x)"
      using coefficient_normalization coefficient_tilde_normalization
      by (simp add: fun_eq_iff algebra_simps)
  qed
  have potential_difference_lp:
      "aim_complex_lp_on_plane p (\<lambda>x. V x - V_tilde x)"
    using scaled_difference_lp unfolding potential_difference_eq .
  have Q_lp: "aim_complex_lp_on_plane p ?Q"
    by (rule slp_restriction_lp_norm_contraction(1)[OF exponent_positive
          Omega_measurable potential_difference_lp])
  have Q_outside: "\<And>z. z \<notin> Omega \<Longrightarrow> ?Q z = 0"
    by (simp add: slp_restrict_field_def)
  have Q_integrable: "integrable lborel ?Q"
    by (rule aim_complex_lp_on_plane_integrable_bounded_support[
      OF exponent_one_le Omega_measurable Omega_bounded Q_lp Q_outside])

  have interior_pairing:
      "\<And>phi. slp_test_function_on Omega phi \<Longrightarrow>
        integral\<^sup>L lborel (\<lambda>z. ?Q z * phi z) = 0"
    by (rule slp_common_cgo_test_pairing_eq_zero[
      OF stationary density fourier_plancherel riesz_hls
        cauchy_test_left_inverse evans_density exponent_lower exponent_upper
        loss_positive loss_upper radius_nonnegative radius_lower set_radius
        center_geometry X_open X_bounded Omega_subset cutoff_test cutoff_one
        cutoff_bound cutoff_derivative_zero_bound cutoff_derivative_one_bound
        A0_nonnegative B0_nonnegative B1_nonnegative coefficient_lp
        coefficient_support coefficient_tilde_lp coefficient_tilde_support
        coefficient_normalization coefficient_tilde_normalization domain
        orthogonality])
  have global_pairing:
      "\<And>phi. hormander_compact_smooth_amplitude phi \<Longrightarrow>
        integral\<^sup>L lborel (\<lambda>z. ?Q z * phi z) = 0"
  proof -
    fix phi :: slp_scalar_field
    assume phi_amplitude: "hormander_compact_smooth_amplitude phi"
    have phi_test: "slp_test_function_on UNIV phi"
      using phi_amplitude
      unfolding hormander_compact_smooth_amplitude_def slp_test_function_on_def
      by blast
    show "integral\<^sup>L lborel (\<lambda>z. ?Q z * phi z) = 0"
      by (rule slp_interior_test_pairing_extends_global[
        OF Omega_open Q_integrable Q_outside interior_pairing phi_test])
  qed
  have Q_zero_AE: "AE x in lborel. ?Q x = 0"
    by (rule slp_compact_smooth_pairing_AE_zero[
      OF exponent_lower Q_lp compact_smooth_density global_pairing])
  have potential_equal_AE:
      "AE x in lborel. x \<in> Omega \<longrightarrow> V x = V_tilde x"
    using Q_zero_AE
  proof eventually_elim
    fix x
    assume Q_zero: "?Q x = 0"
    show "x \<in> Omega \<longrightarrow> V x = V_tilde x"
    proof
      assume x_in: "x \<in> Omega"
      have "V x - V_tilde x = 0"
        using Q_zero x_in by (simp add: slp_restrict_field_def)
      then show "V x = V_tilde x" by simp
    qed
  qed
  show ?thesis
    unfolding slp_potential_ae_equal_def
    using potential_equal_AE Omega_measurable
    by (simp add: AE_restrict_space_iff)
qed

end

end
