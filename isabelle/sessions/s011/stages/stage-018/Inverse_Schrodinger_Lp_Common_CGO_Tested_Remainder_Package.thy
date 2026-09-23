theory Inverse_Schrodinger_Lp_Common_CGO_Tested_Remainder_Package
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_018.Inverse_Schrodinger_Lp_Common_CGO_Tested_Remainder_Bound"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_017.Inverse_Schrodinger_Lp_Common_CGO_Born_Finite_Remainder"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Common-CGO finite identity and tested-remainder bound\<close>

context slp_cgo_full_weak_solution_context
begin

theorem slp_common_cgo_born_finite_families_eq_neg_remainder_with_bound:
  fixes p epsilon A R A0 B0 B1 :: real
    and Omega X :: "slp_point set"
    and phi cutoff coefficient coefficient_tilde V V_tilde :: slp_scalar_field
  assumes riesz_hls: "aim_planar_riesz_hls_claim"
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
    and coefficient_support: "{x. coefficient x \<noteq> 0} \<subseteq> X"
    and coefficient_tilde_lp:
      "aim_complex_lp_on_plane p coefficient_tilde"
    and coefficient_tilde_support:
      "{x. coefficient_tilde x \<noteq> 0} \<subseteq> X"
    and coefficient_normalization: "coefficient = (\<lambda>z. V z / 4)"
    and coefficient_tilde_normalization:
      "coefficient_tilde = (\<lambda>z. V_tilde z / 4)"
    and domain: "slp_bounded_smooth_domain Omega"
    and orthogonality:
      "slp_alessandrini_orthogonality Omega V V_tilde"
    and phi_test: "slp_test_function_on Omega phi"
  shows
    "\<exists>T Z C CV C_tilde CV_tilde.
      (2 \<le> T
      \<and> Z \<in> sets (lborel :: slp_point measure)
      \<and> Z \<noteq> {}
      \<and> Z \<subseteq> Omega
      \<and> (AE c in (lborel :: slp_point measure).
        c \<in> Omega \<longleftrightarrow> c \<in> Z)
      \<and> slp_left_neumann_joint_geometric_data
        p epsilon X Z cutoff coefficient C CV T
      \<and> slp_right_neumann_joint_geometric_data
        p epsilon X Z cutoff coefficient_tilde C_tilde CV_tilde T
      \<and> (\<forall>tau c z. T \<le> tau \<and> c \<in> Z \<longrightarrow>
        slp_left_neumann_joint_series_on
          Z X tau cutoff coefficient (c, z) =
            slp_left_neumann_series_sum X tau c cutoff coefficient z
        \<and> slp_right_neumann_joint_series_on
          Z X tau cutoff coefficient_tilde (c, z) =
            slp_right_neumann_series_sum
              X tau c cutoff coefficient_tilde z)
      \<and> (\<forall>N M tau. T \<le> tau \<longrightarrow>
        slp_leading_functional tau phi
            (slp_restrict_field Omega (\<lambda>x. V x - V_tilde x)) +
          (\<Sum>j<N. slp_left_born_functional j tau phi
            (slp_restrict_field Omega (\<lambda>x. V x - V_tilde x))
            cutoff coefficient SLP_Dbar_Inverse) +
          (\<Sum>k<M. slp_right_born_functional k tau phi
            (slp_restrict_field Omega (\<lambda>x. V x - V_tilde x))
            cutoff coefficient_tilde SLP_Partial_Inverse) +
          (\<Sum>j<N. \<Sum>k<M. slp_mixed_born_functional j k tau phi
            (slp_restrict_field Omega (\<lambda>x. V x - V_tilde x))
            cutoff coefficient coefficient_tilde
            SLP_Dbar_Inverse SLP_Partial_Inverse) =
          - slp_cgo_born_tested_neumann_remainder_functional
              X N M tau phi
              (slp_restrict_field Omega (\<lambda>x. V x - V_tilde x))
              cutoff coefficient coefficient_tilde)
      \<and> (\<forall>N M tau. T \<le> tau \<longrightarrow>
        integrable lborel (\<lambda>c. phi c * integral\<^sup>L lborel (\<lambda>z.
          slp_restrict_field Omega (\<lambda>x. V x - V_tilde x) z *
          slp_cgo_born_neumann_remainder
            X N M tau c cutoff coefficient coefficient_tilde z))
        \<and> norm (slp_cgo_born_tested_neumann_remainder_functional
          X N M tau phi
          (slp_restrict_field Omega (\<lambda>x. V x - V_tilde x))
          cutoff coefficient coefficient_tilde) \<le>
          (tau / pi) *
          (integral\<^sup>L lborel (\<lambda>c. norm (phi c) *
            slp_common_cgo_born_geometric_majorant
              N M p epsilon C CV C_tilde CV_tilde tau
              coefficient coefficient_tilde c)) *
          (integral\<^sup>L lborel (\<lambda>z.
            norm (slp_restrict_field Omega
              (\<lambda>x. V x - V_tilde x) z)))))"
proof -
  let ?Q = "slp_restrict_field Omega (\<lambda>x. V x - V_tilde x)"
  obtain T Z C CV C_tilde CV_tilde where package:
      "2 \<le> T
      \<and> Z \<in> sets (lborel :: slp_point measure)
      \<and> Z \<noteq> {}
      \<and> Z \<subseteq> Omega
      \<and> (AE c in (lborel :: slp_point measure).
        c \<in> Omega \<longleftrightarrow> c \<in> Z)
      \<and> slp_left_neumann_joint_geometric_data
        p epsilon X Z cutoff coefficient C CV T
      \<and> slp_right_neumann_joint_geometric_data
        p epsilon X Z cutoff coefficient_tilde C_tilde CV_tilde T
      \<and> (\<forall>tau c z. T \<le> tau \<and> c \<in> Z \<longrightarrow>
        slp_left_neumann_joint_series_on
          Z X tau cutoff coefficient (c, z) =
            slp_left_neumann_series_sum X tau c cutoff coefficient z
        \<and> slp_right_neumann_joint_series_on
          Z X tau cutoff coefficient_tilde (c, z) =
            slp_right_neumann_series_sum
              X tau c cutoff coefficient_tilde z)
      \<and> (\<forall>N M tau. T \<le> tau \<longrightarrow>
        slp_leading_functional tau phi ?Q +
          (\<Sum>j<N. slp_left_born_functional j tau phi ?Q
            cutoff coefficient SLP_Dbar_Inverse) +
          (\<Sum>k<M. slp_right_born_functional k tau phi ?Q
            cutoff coefficient_tilde SLP_Partial_Inverse) +
          (\<Sum>j<N. \<Sum>k<M. slp_mixed_born_functional j k tau phi ?Q
            cutoff coefficient coefficient_tilde
            SLP_Dbar_Inverse SLP_Partial_Inverse) =
          - slp_cgo_born_tested_neumann_remainder_functional
              X N M tau phi ?Q cutoff coefficient coefficient_tilde)"
    using slp_common_cgo_born_finite_families_eq_neg_remainder[
      OF riesz_hls cauchy_test_left_inverse evans_density
        exponent_lower exponent_upper loss_positive loss_upper
        radius_nonnegative radius_lower set_radius center_geometry X_open
        X_bounded Omega_subset cutoff_test cutoff_one cutoff_bound
        cutoff_derivative_zero_bound cutoff_derivative_one_bound
        A0_nonnegative B0_nonnegative B1_nonnegative coefficient_lp
        coefficient_support coefficient_tilde_lp coefficient_tilde_support
        coefficient_normalization coefficient_tilde_normalization domain
        orthogonality phi_test]
    by blast

  have X_measurable: "X \<in> sets lborel"
    using X_open by simp
  have Omega_measurable: "Omega \<in> sets lborel"
    using slp_bounded_smooth_domain_lborel_carrier[OF domain] by blast
  have cutoff_smooth: "smooth_on UNIV cutoff"
    using cutoff_test unfolding slp_test_function_on_def by blast
  have cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    using borel_measurable_continuous_onI[
      OF smooth_on_imp_continuous_on[OF cutoff_smooth]] by simp
  have exponent_one_le: "1 \<le> p"
    using exponent_lower by linarith
  have exponent_positive: "0 < p"
    using exponent_lower by linarith
  have coefficient_difference_lp:
      "aim_complex_lp_on_plane p (\<lambda>x. coefficient x - coefficient_tilde x)"
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
  have carrier_AE:
      "AE c in (lborel :: slp_point measure).
        c \<in> Omega \<longleftrightarrow> c \<in> Z"
    using package by blast
  have left_data:
      "slp_left_neumann_joint_geometric_data
        p epsilon X Z cutoff coefficient C CV T"
    using package by blast
  have right_data:
      "slp_right_neumann_joint_geometric_data
        p epsilon X Z cutoff coefficient_tilde C_tilde CV_tilde T"
    using package by blast
  have quantitative:
      "\<forall>N M tau. T \<le> tau \<longrightarrow>
        integrable lborel (\<lambda>c. phi c * integral\<^sup>L lborel (\<lambda>z.
          ?Q z * slp_cgo_born_neumann_remainder
            X N M tau c cutoff coefficient coefficient_tilde z))
        \<and> norm (slp_cgo_born_tested_neumann_remainder_functional
          X N M tau phi ?Q cutoff coefficient coefficient_tilde) \<le>
          (tau / pi) *
          (integral\<^sup>L lborel (\<lambda>c. norm (phi c) *
            slp_common_cgo_born_geometric_majorant
              N M p epsilon C CV C_tilde CV_tilde tau
              coefficient coefficient_tilde c)) *
          (integral\<^sup>L lborel (\<lambda>z. norm (?Q z)))"
  proof (intro allI impI)
    fix N M tau
    assume tau_lower: "T \<le> tau"
    show
      "integrable lborel (\<lambda>c. phi c * integral\<^sup>L lborel (\<lambda>z.
          ?Q z * slp_cgo_born_neumann_remainder
            X N M tau c cutoff coefficient coefficient_tilde z))
       \<and> norm (slp_cgo_born_tested_neumann_remainder_functional
          X N M tau phi ?Q cutoff coefficient coefficient_tilde) \<le>
          (tau / pi) *
          (integral\<^sup>L lborel (\<lambda>c. norm (phi c) *
            slp_common_cgo_born_geometric_majorant
              N M p epsilon C CV C_tilde CV_tilde tau
              coefficient coefficient_tilde c)) *
          (integral\<^sup>L lborel (\<lambda>z. norm (?Q z)))"
      by (rule slp_common_cgo_born_tested_neumann_remainder_bound[
        OF exponent_lower exponent_upper X_measurable X_bounded Omega_subset
          Q_lp Q_outside cutoff_measurable coefficient_lp coefficient_tilde_lp
          phi_test carrier_AE left_data right_data tau_lower tau_lower])
  qed

  show ?thesis
    apply (rule exI[of _ T], rule exI[of _ Z], rule exI[of _ C],
      rule exI[of _ CV], rule exI[of _ C_tilde],
      rule exI[of _ CV_tilde])
    using package quantitative by blast
qed

end

end
