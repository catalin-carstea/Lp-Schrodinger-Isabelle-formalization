theory Inverse_Schrodinger_Lp_Common_CGO_Test_Pairing_Zero
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_018.Inverse_Schrodinger_Lp_Common_CGO_Leading_Functional_Decay"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_013.Inverse_Schrodinger_Lp_Center_Average_Smooth_Convergence"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Recovery of the compact-smooth test pairing\<close>

context slp_cgo_full_weak_solution_context
begin

theorem slp_common_cgo_test_pairing_eq_zero:
  fixes p epsilon A R A0 B0 B1 :: real
    and Omega X :: "slp_point set"
    and phi cutoff coefficient coefficient_tilde V V_tilde :: slp_scalar_field
  assumes stationary:
      "hormander_quadratic_stationary_phase_decay_claim TYPE(2)"
    and density: "evans_compact_smooth_l1_density_claim TYPE(2)"
    and fourier_plancherel:
      "hormander_euclidean_l2_fourier_plancherel_claim"
    and riesz_hls: "aim_planar_riesz_hls_claim"
    and cauchy_test_left_inverse:
      "aim_planar_cauchy_test_left_inverse_claim"
    and evans_density: "evans_compact_support_w1p_zero_density_claim"
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
    and phi_test: "slp_test_function_on Omega phi"
  defines
    "N \<equiv> nat
      (slp_tail_cutoff1
        (1 - 1 / p - epsilon) (1 - 1 / p - epsilon))"
  shows
    "integral\<^sup>L lborel (\<lambda>z.
      slp_restrict_field Omega (\<lambda>x. V x - V_tilde x) z * phi z) = 0"
proof -
  interpret hf: hormander_euclidean_l2_fourier_plancherel
    by standard (rule fourier_plancherel)
  let ?Q = "slp_restrict_field Omega (\<lambda>x. V x - V_tilde x)"
  have Omega_measurable: "Omega \<in> sets lborel"
    using slp_bounded_smooth_domain_lborel_carrier[OF domain] by blast
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
  have phi_test_UNIV: "slp_test_function_on UNIV phi"
    using phi_test unfolding slp_test_function_on_def by blast

  have leading_zero:
      "((\<lambda>tau :: real. slp_leading_functional tau phi ?Q)
        \<longlongrightarrow> 0) at_top"
    unfolding N_def
    by (rule slp_common_cgo_leading_functional_tendsto_zero[
      OF stationary density fourier_plancherel riesz_hls
        cauchy_test_left_inverse evans_density exponent_lower exponent_upper
        loss_positive loss_upper radius_nonnegative radius_lower set_radius
        center_geometry X_open X_bounded Omega_subset cutoff_test cutoff_one
        cutoff_bound cutoff_derivative_zero_bound cutoff_derivative_one_bound
        A0_nonnegative B0_nonnegative B1_nonnegative coefficient_lp
        coefficient_support coefficient_tilde_lp coefficient_tilde_support
        coefficient_normalization coefficient_tilde_normalization domain
        orthogonality phi_test])
  have leading_pairing:
      "((\<lambda>tau :: real. slp_leading_functional tau phi ?Q)
        \<longlongrightarrow> integral\<^sup>L lborel (\<lambda>z. ?Q z * phi z)) at_top"
    by (rule hf.slp_leading_functional_smooth_limit[
      OF Q_integrable phi_test_UNIV])
  show ?thesis
    by (rule tendsto_unique[
      OF trivial_limit_at_top_linorder leading_pairing leading_zero])
qed

end

end
