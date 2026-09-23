theory Inverse_Schrodinger_Lp_Common_CGO_Alessandrini_Born_Family
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_017.Inverse_Schrodinger_Lp_Two_Coefficient_Common_Both_Center"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Common literal-CGO family in the frozen orthogonality identity\<close>

context slp_cgo_full_weak_solution_context
begin

theorem slp_common_literal_cgo_alessandrini_born_family:
  fixes p epsilon A R A0 B0 B1 :: real
    and Omega X :: "slp_point set"
    and cutoff coefficient coefficient_tilde V V_tilde :: slp_scalar_field
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
  shows
    "\<exists>T Z. 2 \<le> T
      \<and> Z \<in> sets (lborel :: slp_point measure)
      \<and> Z \<noteq> {}
      \<and> Z \<subseteq> Omega
      \<and> (AE c in (lborel :: slp_point measure).
        c \<in> Omega \<longleftrightarrow> c \<in> Z)
      \<and> (\<forall>tau c. T \<le> tau \<longrightarrow> c \<in> Z \<longrightarrow>
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
                  X tau c cutoff coefficient_tilde x)) = 0)"
proof -
  obtain T Z where T_lower: "2 \<le> T"
    and Z_measurable:
      "Z \<in> sets (lborel :: slp_point measure)"
    and Z_nonempty: "Z \<noteq> {}"
    and Z_subset: "Z \<subseteq> Omega"
    and Z_AE:
      "AE c in (lborel :: slp_point measure).
        c \<in> Omega \<longleftrightarrow> c \<in> Z"
    and center_data:
      "\<forall>c \<in> Z.
        slp_left_neumann_center_fixed_point_data
          X T c cutoff coefficient
        \<and> slp_left_neumann_center_fixed_point_data
          X T c cutoff coefficient_tilde
        \<and> slp_right_neumann_center_fixed_point_data
          X T c cutoff coefficient
        \<and> slp_right_neumann_center_fixed_point_data
          X T c cutoff coefficient_tilde"
    using slp_two_coefficient_common_both_center_fixed_point[
      OF riesz_hls cauchy_test_left_inverse evans_density
        exponent_lower exponent_upper loss_positive loss_upper
        radius_nonnegative radius_lower set_radius center_geometry
        X_open X_bounded cutoff_test cutoff_bound
        cutoff_derivative_zero_bound cutoff_derivative_one_bound
        A0_nonnegative B0_nonnegative B1_nonnegative
        coefficient_lp coefficient_support coefficient_tilde_lp
        coefficient_tilde_support domain]
    by blast
  have Omega_measurable:
      "Omega \<in> sets (lborel :: slp_point measure)"
    using slp_bounded_smooth_domain_lborel_carrier[OF domain] by blast
  have Omega_bounded: "bounded Omega"
    using domain unfolding slp_bounded_smooth_domain_def by blast

  have born_family:
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
  proof (intro allI impI)
    fix tau c
    assume tau_lower: "T \<le> tau"
      and c_in: "c \<in> Z"
    note all_data = center_data[rule_format, OF c_in]
    have left_data:
        "slp_left_neumann_center_fixed_point_data
          X T c cutoff coefficient"
      using all_data by blast
    have left_tilde_data:
        "slp_left_neumann_center_fixed_point_data
          X T c cutoff coefficient_tilde"
      using all_data by blast
    have right_data:
        "slp_right_neumann_center_fixed_point_data
          X T c cutoff coefficient"
      using all_data by blast
    have right_tilde_data:
        "slp_right_neumann_center_fixed_point_data
          X T c cutoff coefficient_tilde"
      using all_data by blast

    obtain M_left where left_admissible:
        "slp_ae_bounded_measurable lborel M_left
          (slp_left_neumann_series_sum X tau c cutoff coefficient)"
      and left_fixed:
        "AE z in lborel.
          slp_left_neumann_series_sum X tau c cutoff coefficient z =
            slp_restrict_field X
              (slp_left_neumann_base tau c cutoff coefficient
                SLP_Dbar_Inverse) z +
            slp_restrict_field X
              (slp_left_neumann_step tau c cutoff coefficient
                (slp_left_neumann_series_sum
                  X tau c cutoff coefficient)) z"
      using left_data tau_lower
      unfolding slp_left_neumann_center_fixed_point_data_def by blast
    obtain M_left_tilde where left_tilde_admissible:
        "slp_ae_bounded_measurable lborel M_left_tilde
          (slp_left_neumann_series_sum X tau c cutoff coefficient_tilde)"
      and left_tilde_fixed:
        "AE z in lborel.
          slp_left_neumann_series_sum X tau c cutoff coefficient_tilde z =
            slp_restrict_field X
              (slp_left_neumann_base tau c cutoff coefficient_tilde
                SLP_Dbar_Inverse) z +
            slp_restrict_field X
              (slp_left_neumann_step tau c cutoff coefficient_tilde
                (slp_left_neumann_series_sum
                  X tau c cutoff coefficient_tilde)) z"
      using left_tilde_data tau_lower
      unfolding slp_left_neumann_center_fixed_point_data_def by blast
    obtain M_right where right_admissible:
        "slp_ae_bounded_measurable lborel M_right
          (slp_right_neumann_series_sum X tau c cutoff coefficient)"
      and right_fixed:
        "AE z in lborel.
          slp_right_neumann_series_sum X tau c cutoff coefficient z =
            slp_restrict_field X
              (slp_right_neumann_base tau c cutoff coefficient
                SLP_Partial_Inverse) z +
            slp_restrict_field X
              (slp_right_neumann_step tau c cutoff coefficient
                (slp_right_neumann_series_sum
                  X tau c cutoff coefficient)) z"
      using right_data tau_lower
      unfolding slp_right_neumann_center_fixed_point_data_def by blast
    obtain M_right_tilde where right_tilde_admissible:
        "slp_ae_bounded_measurable lborel M_right_tilde
          (slp_right_neumann_series_sum X tau c cutoff coefficient_tilde)"
      and right_tilde_fixed:
        "AE z in lborel.
          slp_right_neumann_series_sum X tau c cutoff coefficient_tilde z =
            slp_restrict_field X
              (slp_right_neumann_base tau c cutoff coefficient_tilde
                SLP_Partial_Inverse) z +
            slp_restrict_field X
              (slp_right_neumann_step tau c cutoff coefficient_tilde
                (slp_right_neumann_series_sum
                  X tau c cutoff coefficient_tilde)) z"
      using right_tilde_data tau_lower
      unfolding slp_right_neumann_center_fixed_point_data_def by blast

    note coefficient_solutions =
      slp_both_affine_fixed_point_cgo_fields_weak_solution[
        OF exponent_lower exponent_upper X_open X_bounded
          Omega_measurable Omega_bounded Omega_subset cutoff_test cutoff_one
          coefficient_lp coefficient_support coefficient_normalization
          left_admissible right_admissible left_fixed right_fixed]
    note coefficient_tilde_solutions =
      slp_both_affine_fixed_point_cgo_fields_weak_solution[
        OF exponent_lower exponent_upper X_open X_bounded
          Omega_measurable Omega_bounded Omega_subset cutoff_test cutoff_one
          coefficient_tilde_lp coefficient_tilde_support
          coefficient_tilde_normalization left_tilde_admissible
          right_tilde_admissible left_tilde_fixed right_tilde_fixed]
    have left_solution:
        "slp_weak_solution Omega V
          (slp_left_cgo_field tau c
              (slp_left_neumann_series_sum X tau c cutoff coefficient),
            slp_left_cgo_gradient tau c
              (slp_left_neumann_series_sum X tau c cutoff coefficient)
              (slp_left_outer_conjugated_gradient tau c cutoff coefficient
                (slp_left_neumann_series_sum
                  X tau c cutoff coefficient)))"
      using coefficient_solutions by blast
    have right_tilde_solution:
        "slp_weak_solution Omega V_tilde
          (slp_right_cgo_field tau c
              (slp_right_neumann_series_sum
                X tau c cutoff coefficient_tilde),
            slp_right_cgo_gradient tau c
              (slp_right_neumann_series_sum
                X tau c cutoff coefficient_tilde)
              (slp_right_outer_conjugated_gradient tau c cutoff
                coefficient_tilde
                (slp_right_neumann_series_sum
                  X tau c cutoff coefficient_tilde)))"
      using coefficient_tilde_solutions by blast
    show
      "set_integrable lborel Omega
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
      by (rule slp_alessandrini_literal_cgo_born_identity[
            OF orthogonality left_solution right_tilde_solution])
  qed
  show ?thesis
    using T_lower Z_measurable Z_nonempty Z_subset Z_AE born_family by blast
qed

end

end
