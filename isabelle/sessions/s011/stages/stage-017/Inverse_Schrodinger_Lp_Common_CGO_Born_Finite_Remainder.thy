theory Inverse_Schrodinger_Lp_Common_CGO_Born_Finite_Remainder
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_017.Inverse_Schrodinger_Lp_CGO_Born_Domain_Carrier_Closure"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_010.Inverse_Schrodinger_Lp_Complex_Lp_Coarse_Triangle"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_012.Inverse_Schrodinger_Lp_Bounded_Support_Lp_Norm"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Common-CGO finite Born family and exact Neumann remainder\<close>

context slp_cgo_full_weak_solution_context
begin

theorem slp_common_cgo_born_finite_families_eq_neg_remainder:
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
      2 \<le> T
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
              cutoff coefficient coefficient_tilde)"
proof -
  obtain T Z C CV C_tilde CV_tilde where T_lower: "2 \<le> T"
    and Z_measurable: "Z \<in> sets (lborel :: slp_point measure)"
    and Z_nonempty: "Z \<noteq> {}"
    and Z_subset: "Z \<subseteq> Omega"
    and Z_AE:
      "AE c in (lborel :: slp_point measure).
        c \<in> Omega \<longleftrightarrow> c \<in> Z"
    and left_data:
      "slp_left_neumann_joint_geometric_data
        p epsilon X Z cutoff coefficient C CV T"
    and right_data:
      "slp_right_neumann_joint_geometric_data
        p epsilon X Z cutoff coefficient_tilde C_tilde CV_tilde T"
    and fibers:
      "\<forall>tau c z. T \<le> tau \<and> c \<in> Z \<longrightarrow>
        slp_left_neumann_joint_series_on
          Z X tau cutoff coefficient (c, z) =
            slp_left_neumann_series_sum X tau c cutoff coefficient z
        \<and> slp_right_neumann_joint_series_on
          Z X tau cutoff coefficient_tilde (c, z) =
            slp_right_neumann_series_sum
              X tau c cutoff coefficient_tilde z"
    and born:
      "\<forall>tau c. T \<le> tau \<longrightarrow> c \<in> Z \<longrightarrow>
        set_integrable lborel Omega
          (\<lambda>x. (V x - V_tilde x) *
            (slp_center_kernel tau c x +
              slp_left_neumann_series_sum
                X tau c cutoff coefficient x +
              slp_right_neumann_series_sum
                X tau c cutoff coefficient_tilde x +
              slp_center_kernel (- tau) c x *
                slp_left_neumann_series_sum
                  X tau c cutoff coefficient x *
                slp_right_neumann_series_sum
                  X tau c cutoff coefficient_tilde x))
        \<and>
        set_lebesgue_integral lborel Omega
          (\<lambda>x. (V x - V_tilde x) *
            (slp_center_kernel tau c x +
              slp_left_neumann_series_sum
                X tau c cutoff coefficient x +
              slp_right_neumann_series_sum
                X tau c cutoff coefficient_tilde x +
              slp_center_kernel (- tau) c x *
                slp_left_neumann_series_sum
                  X tau c cutoff coefficient x *
                slp_right_neumann_series_sum
                  X tau c cutoff coefficient_tilde x)) = 0"
    using slp_common_cgo_born_joint_series[
      OF riesz_hls cauchy_test_left_inverse evans_density
        exponent_lower exponent_upper loss_positive loss_upper
        radius_nonnegative radius_lower set_radius center_geometry
        X_open X_bounded Omega_subset cutoff_test cutoff_one cutoff_bound
        cutoff_derivative_zero_bound cutoff_derivative_one_bound
        A0_nonnegative B0_nonnegative B1_nonnegative coefficient_lp
        coefficient_support coefficient_tilde_lp coefficient_tilde_support
        coefficient_normalization coefficient_tilde_normalization domain
        orthogonality]
    by blast

  have exponent_one_le: "1 \<le> p"
    using exponent_lower by linarith
  have exponent_positive: "0 < p"
    using exponent_lower by linarith
  have X_measurable: "X \<in> sets lborel"
    using X_open by simp
  have Omega_measurable: "Omega \<in> sets lborel"
    using slp_bounded_smooth_domain_lborel_carrier[OF domain] by blast
  have cutoff_smooth: "smooth_on UNIV cutoff"
    using cutoff_test unfolding slp_test_function_on_def by blast
  have cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    using borel_measurable_continuous_onI[
      OF smooth_on_imp_continuous_on[OF cutoff_smooth]] by simp
  have cutoff_support_X: "{x. cutoff x \<noteq> 0} \<subseteq> X"
  proof
    fix x
    assume x_nonzero: "x \<in> {x. cutoff x \<noteq> 0}"
    have "x \<in> closure {x. cutoff x \<noteq> 0}"
      using x_nonzero by (rule subsetD[OF closure_subset])
    then show "x \<in> X"
      using cutoff_test unfolding slp_test_function_on_def by blast
  qed
  have cutoff_bound_global: "\<And>x. norm (cutoff x) \<le> A0"
  proof -
    fix x
    show "norm (cutoff x) \<le> A0"
    proof (cases "x \<in> X")
      case True
      then show ?thesis by (rule cutoff_bound)
    next
      case False
      have "cutoff x = 0" using cutoff_support_X False by blast
      then show ?thesis using A0_nonnegative by simp
    qed
  qed
  have cutoff_support_radius:
      "\<And>x. cutoff x \<noteq> 0 \<Longrightarrow> norm x \<le> A"
    using cutoff_support_X set_radius by blast
  have coefficient_support_radius:
      "\<And>x. coefficient x \<noteq> 0 \<Longrightarrow> norm x \<le> A"
    using coefficient_support set_radius by blast
  have coefficient_tilde_support_radius:
      "\<And>x. coefficient_tilde x \<noteq> 0 \<Longrightarrow> norm x \<le> A"
    using coefficient_tilde_support set_radius by blast

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
          OF exponent_positive
          four_measurable _ _ coefficient_difference_lp]) simp_all
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
  let ?Q = "slp_restrict_field Omega (\<lambda>x. V x - V_tilde x)"
  have Q_lp: "aim_complex_lp_on_plane p ?Q"
    by (rule slp_restriction_lp_norm_contraction(1)[OF exponent_positive
          Omega_measurable potential_difference_lp])
  have Q_outside: "\<And>x. x \<notin> Omega \<Longrightarrow> ?Q x = 0"
    by (simp add: slp_restrict_field_def)
  have Q_support_radius: "\<And>x. ?Q x \<noteq> 0 \<Longrightarrow> norm x \<le> A"
  proof -
    fix x
    assume Q_nonzero: "?Q x \<noteq> 0"
    have x_Omega: "x \<in> Omega"
      using Q_nonzero by (cases "x \<in> Omega")
        (simp_all add: slp_restrict_field_def)
    have "x \<in> X" using Omega_subset x_Omega by blast
    then show "norm x \<le> A" by (rule set_radius)
  qed
  have finite_context: "aim_planar_riesz_hls_cauchy"
    using riesz_hls aim_planar_hls_cauchy by unfold_locales

  show ?thesis
  proof (rule exI[of _ T], rule exI[of _ Z], rule exI[of _ C],
      rule exI[of _ CV], rule exI[of _ C_tilde],
      rule exI[of _ CV_tilde])
    show
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
    proof (intro conjI)
      show "2 \<le> T" by (rule T_lower)
      show "Z \<in> sets (lborel :: slp_point measure)"
        by (rule Z_measurable)
      show "Z \<noteq> {}" by (rule Z_nonempty)
      show "Z \<subseteq> Omega" by (rule Z_subset)
      show "AE c in (lborel :: slp_point measure).
          c \<in> Omega \<longleftrightarrow> c \<in> Z"
        by (rule Z_AE)
      show "slp_left_neumann_joint_geometric_data
          p epsilon X Z cutoff coefficient C CV T"
        by (rule left_data)
      show "slp_right_neumann_joint_geometric_data
          p epsilon X Z cutoff coefficient_tilde C_tilde CV_tilde T"
        by (rule right_data)
      show "\<forall>tau c z. T \<le> tau \<and> c \<in> Z \<longrightarrow>
          slp_left_neumann_joint_series_on
            Z X tau cutoff coefficient (c, z) =
              slp_left_neumann_series_sum X tau c cutoff coefficient z
          \<and> slp_right_neumann_joint_series_on
            Z X tau cutoff coefficient_tilde (c, z) =
              slp_right_neumann_series_sum
                X tau c cutoff coefficient_tilde z"
        by (rule fibers)
      show
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
      proof (intro allI impI)
    fix N M tau
    assume tau_large: "T \<le> tau"
    have born_integrable_Q:
        "\<And>c. c \<in> Z \<Longrightarrow> set_integrable lborel Omega
          (\<lambda>z. ?Q z * slp_cgo_born_neumann_bracket
            X tau c cutoff coefficient coefficient_tilde z)"
    proof -
      fix c
      assume c_in: "c \<in> Z"
      note raw = conjunct1[OF born[rule_format, OF tau_large c_in]]
      have integrability_equality:
          "set_integrable lborel Omega
              (\<lambda>z. ?Q z * slp_cgo_born_neumann_bracket
                X tau c cutoff coefficient coefficient_tilde z) =
            set_integrable lborel Omega
              (\<lambda>z. (V z - V_tilde z) *
                (slp_center_kernel tau c z +
                  slp_left_neumann_series_sum
                    X tau c cutoff coefficient z +
                  slp_right_neumann_series_sum
                    X tau c cutoff coefficient_tilde z +
                  slp_center_kernel (- tau) c z *
                    slp_left_neumann_series_sum
                      X tau c cutoff coefficient z *
                    slp_right_neumann_series_sum
                      X tau c cutoff coefficient_tilde z))"
      proof (rule set_integrable_cong)
        show "lborel = lborel" by (rule refl)
        show "Omega = Omega" by (rule refl)
        fix z
        assume "z \<in> Omega"
        then show
          "?Q z * slp_cgo_born_neumann_bracket
                X tau c cutoff coefficient coefficient_tilde z =
            (V z - V_tilde z) *
              (slp_center_kernel tau c z +
                slp_left_neumann_series_sum
                  X tau c cutoff coefficient z +
                slp_right_neumann_series_sum
                  X tau c cutoff coefficient_tilde z +
                slp_center_kernel (- tau) c z *
                  slp_left_neumann_series_sum
                    X tau c cutoff coefficient z *
                  slp_right_neumann_series_sum
                    X tau c cutoff coefficient_tilde z)"
          by (simp add: slp_restrict_field_def
              slp_cgo_born_neumann_bracket_def)
      qed
      show "set_integrable lborel Omega
          (\<lambda>z. ?Q z * slp_cgo_born_neumann_bracket
            X tau c cutoff coefficient coefficient_tilde z)"
        using raw integrability_equality by blast
    qed
    have born_zero_Q:
        "\<And>c. c \<in> Z \<Longrightarrow> set_lebesgue_integral lborel Omega
          (\<lambda>z. ?Q z * slp_cgo_born_neumann_bracket
            X tau c cutoff coefficient coefficient_tilde z) = 0"
    proof -
      fix c
      assume c_in: "c \<in> Z"
      note raw = conjunct2[OF born[rule_format, OF tau_large c_in]]
      have integral_equality:
          "set_lebesgue_integral lborel Omega
              (\<lambda>z. ?Q z * slp_cgo_born_neumann_bracket
                X tau c cutoff coefficient coefficient_tilde z) =
            set_lebesgue_integral lborel Omega
              (\<lambda>z. (V z - V_tilde z) *
                (slp_center_kernel tau c z +
                  slp_left_neumann_series_sum
                    X tau c cutoff coefficient z +
                  slp_right_neumann_series_sum
                    X tau c cutoff coefficient_tilde z +
                  slp_center_kernel (- tau) c z *
                    slp_left_neumann_series_sum
                      X tau c cutoff coefficient z *
                    slp_right_neumann_series_sum
                      X tau c cutoff coefficient_tilde z))"
      proof (rule set_lebesgue_integral_cong[OF Omega_measurable])
        show "\<forall>z. z \<in> Omega \<longrightarrow>
          ?Q z * slp_cgo_born_neumann_bracket
                X tau c cutoff coefficient coefficient_tilde z =
            (V z - V_tilde z) *
              (slp_center_kernel tau c z +
                slp_left_neumann_series_sum
                  X tau c cutoff coefficient z +
                slp_right_neumann_series_sum
                  X tau c cutoff coefficient_tilde z +
                slp_center_kernel (- tau) c z *
                  slp_left_neumann_series_sum
                    X tau c cutoff coefficient z *
                  slp_right_neumann_series_sum
                    X tau c cutoff coefficient_tilde z)"
          by (intro allI impI)
            (simp add: slp_restrict_field_def
              slp_cgo_born_neumann_bracket_def)
      qed
      show "set_lebesgue_integral lborel Omega
          (\<lambda>z. ?Q z * slp_cgo_born_neumann_bracket
            X tau c cutoff coefficient coefficient_tilde z) = 0"
        using raw integral_equality by simp
    qed
    note finite_closure = aim_planar_riesz_hls_cauchy.slp_cgo_born_domain_carrier_finite_families_eq_neg_remainder[
        OF finite_context radius_nonnegative A0_nonnegative
          exponent_lower exponent_upper
          X_measurable X_bounded Omega_subset cutoff_measurable coefficient_lp
          coefficient_tilde_lp Q_lp Q_outside cutoff_bound_global
          Q_support_radius cutoff_support_radius coefficient_support_radius
          coefficient_tilde_support_radius phi_test Z_AE
          born_integrable_Q born_zero_Q]
    show
      "slp_leading_functional tau phi ?Q +
          (\<Sum>j<N. slp_left_born_functional j tau phi ?Q
            cutoff coefficient SLP_Dbar_Inverse) +
          (\<Sum>k<M. slp_right_born_functional k tau phi ?Q
            cutoff coefficient_tilde SLP_Partial_Inverse) +
          (\<Sum>j<N. \<Sum>k<M. slp_mixed_born_functional j k tau phi ?Q
            cutoff coefficient coefficient_tilde
            SLP_Dbar_Inverse SLP_Partial_Inverse) =
          - slp_cgo_born_tested_neumann_remainder_functional
              X N M tau phi ?Q cutoff coefficient coefficient_tilde"
      by (rule finite_closure)
      qed
    qed
  qed
qed

end

end
