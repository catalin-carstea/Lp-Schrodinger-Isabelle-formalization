theory Inverse_Schrodinger_Lp_Common_CGO_Leading_Functional_Decay
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_018.Inverse_Schrodinger_Lp_Common_CGO_Tested_Remainder_Decay"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_018.Inverse_Schrodinger_Lp_Common_CGO_Finite_Born_Family_Decay"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Decay of the exact common-CGO leading functional\<close>

context slp_cgo_full_weak_solution_context
begin

theorem slp_common_cgo_leading_functional_tendsto_zero:
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
    "((\<lambda>tau :: real.
        slp_leading_functional tau phi
          (slp_restrict_field Omega (\<lambda>x. V x - V_tilde x)))
      \<longlongrightarrow> 0) at_top"
proof -
  let ?Q = "slp_restrict_field Omega (\<lambda>x. V x - V_tilde x)"
  let ?left = "\<lambda>tau :: real. \<Sum>j<N.
    slp_left_born_functional j tau phi ?Q cutoff coefficient
      SLP_Dbar_Inverse"
  let ?right = "\<lambda>tau :: real. \<Sum>k<N.
    slp_right_born_functional k tau phi ?Q cutoff coefficient_tilde
      SLP_Partial_Inverse"
  let ?mixed = "\<lambda>tau :: real. \<Sum>j<N. \<Sum>k<N.
    slp_mixed_born_functional j k tau phi ?Q cutoff coefficient
      coefficient_tilde SLP_Dbar_Inverse SLP_Partial_Inverse"
  let ?remainder = "\<lambda>tau :: real.
    slp_cgo_born_tested_neumann_remainder_functional
      X N N tau phi ?Q cutoff coefficient coefficient_tilde"

  have coefficient_support_X:
      "{x. coefficient x \<noteq> 0} \<subseteq> X"
    using coefficient_support Omega_subset by blast
  have coefficient_tilde_support_X:
      "{x. coefficient_tilde x \<noteq> 0} \<subseteq> X"
    using coefficient_tilde_support Omega_subset by blast
  have X_measurable: "X \<in> sets lborel"
    using X_open by simp
  have Omega_measurable: "Omega \<in> sets lborel"
    using slp_bounded_smooth_domain_lborel_carrier[OF domain] by blast
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
  have Q_support: "{x. ?Q x \<noteq> 0} \<subseteq> Omega"
    by (auto simp: slp_restrict_field_def)

  have remainder_limit: "(?remainder \<longlongrightarrow> 0) at_top"
    unfolding N_def
    by (rule slp_common_cgo_born_tested_neumann_remainder_tendsto_zero[
      OF riesz_hls cauchy_test_left_inverse evans_density exponent_lower
        exponent_upper loss_positive loss_upper radius_nonnegative
        radius_lower set_radius center_geometry X_open X_bounded Omega_subset
        cutoff_test cutoff_one cutoff_bound cutoff_derivative_zero_bound
        cutoff_derivative_one_bound A0_nonnegative B0_nonnegative
        B1_nonnegative coefficient_lp coefficient_support_X
        coefficient_tilde_lp coefficient_tilde_support_X
        coefficient_normalization coefficient_tilde_normalization domain
        orthogonality phi_test])

  have family_limits:
      "(?left \<longlongrightarrow> 0) at_top
      \<and> (?right \<longlongrightarrow> 0) at_top
      \<and> (?mixed \<longlongrightarrow> 0) at_top"
    by (rule slp_common_cgo_finite_born_families_tendsto_zero[
      OF stationary density fourier_plancherel exponent_lower exponent_upper
        X_bounded X_measurable Omega_subset cutoff_test cutoff_one
        coefficient_lp coefficient_support coefficient_tilde_lp
        coefficient_tilde_support Q_lp Q_support phi_test])
  have left_limit: "(?left \<longlongrightarrow> 0) at_top"
    using family_limits by blast
  have right_limit: "(?right \<longlongrightarrow> 0) at_top"
    using family_limits by blast
  have mixed_limit: "(?mixed \<longlongrightarrow> 0) at_top"
    using family_limits by blast

  obtain T where finite_identity:
      "\<forall>N M tau. T \<le> tau \<longrightarrow>
        slp_leading_functional tau phi ?Q +
          (\<Sum>j<N. slp_left_born_functional j tau phi ?Q
            cutoff coefficient SLP_Dbar_Inverse) +
          (\<Sum>k<M. slp_right_born_functional k tau phi ?Q
            cutoff coefficient_tilde SLP_Partial_Inverse) +
          (\<Sum>j<N. \<Sum>k<M. slp_mixed_born_functional j k tau phi ?Q
            cutoff coefficient coefficient_tilde
            SLP_Dbar_Inverse SLP_Partial_Inverse) =
          - slp_cgo_born_tested_neumann_remainder_functional
              X N M tau phi ?Q cutoff coefficient coefficient_tilde"
    using slp_common_cgo_born_finite_families_eq_neg_remainder_with_bound[
      OF riesz_hls cauchy_test_left_inverse evans_density exponent_lower
        exponent_upper loss_positive loss_upper radius_nonnegative
        radius_lower set_radius center_geometry X_open X_bounded Omega_subset
        cutoff_test cutoff_one cutoff_bound cutoff_derivative_zero_bound
        cutoff_derivative_one_bound A0_nonnegative B0_nonnegative
        B1_nonnegative coefficient_lp coefficient_support_X
        coefficient_tilde_lp coefficient_tilde_support_X
        coefficient_normalization coefficient_tilde_normalization domain
        orthogonality phi_test]
    by blast
  have eventual_identity:
      "\<forall>\<^sub>F tau :: real in at_top.
        slp_leading_functional tau phi ?Q =
          - ?remainder tau - ?left tau - ?right tau - ?mixed tau"
    using eventually_ge_at_top[of T]
  proof eventually_elim
    fix tau :: real
    assume tau_large: "T \<le> tau"
    have raw_identity:
        "slp_leading_functional tau phi ?Q + ?left tau + ?right tau +
            ?mixed tau = - ?remainder tau"
      using finite_identity[rule_format, where N=N and M=N and tau=tau]
        tau_large by simp
    have moved_identity:
        "(slp_leading_functional tau phi ?Q + ?left tau + ?right tau +
            ?mixed tau) - ?left tau - ?right tau - ?mixed tau =
          - ?remainder tau - ?left tau - ?right tau - ?mixed tau"
      using raw_identity by simp
    show "slp_leading_functional tau phi ?Q =
        - ?remainder tau - ?left tau - ?right tau - ?mixed tau"
      using moved_identity by (simp add: algebra_simps)
  qed

  have minus_remainder_limit:
      "((\<lambda>tau. - ?remainder tau) \<longlongrightarrow> 0) at_top"
    using tendsto_minus[OF remainder_limit] by simp
  have first_limit:
      "((\<lambda>tau. - ?remainder tau - ?left tau)
        \<longlongrightarrow> 0) at_top"
    using tendsto_diff[OF minus_remainder_limit left_limit] by simp
  have second_limit:
      "((\<lambda>tau. - ?remainder tau - ?left tau - ?right tau)
        \<longlongrightarrow> 0) at_top"
    using tendsto_diff[OF first_limit right_limit] by simp
  have combined_limit:
      "((\<lambda>tau.
          - ?remainder tau - ?left tau - ?right tau - ?mixed tau)
        \<longlongrightarrow> 0) at_top"
    using tendsto_diff[OF second_limit mixed_limit] by simp
  show ?thesis
    by (rule tendsto_cong[OF eventual_identity, THEN iffD2,
          OF combined_limit])
qed

end

end
