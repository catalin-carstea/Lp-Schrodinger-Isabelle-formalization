theory Inverse_Schrodinger_Lp_Right_Neumann_Step_AE_Contraction
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_016.Inverse_Schrodinger_Lp_Right_Neumann_Iterate_Geometric_Contraction"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_015.Inverse_Schrodinger_Lp_AE_Neumann_Sum_Fixed_Point"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Literal right Neumann step on AE-bounded measurable fields\<close>

context slp_cauchy_local_w1s
begin

theorem slp_right_neumann_step_restricted_ae_contraction:
  fixes p epsilon A R A0 B0 B1 :: real
    and X :: "slp_point set"
    and cutoff coefficient :: slp_scalar_field
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
    and X_open: "open X"
    and X_bounded: "bounded X"
    and cutoff_test: "slp_test_function_on X cutoff"
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
  shows
    "\<exists>T::real. 2 \<le> T \<and>
      (\<forall>tau c multiplier M.
        T \<le> tau \<and>
        (\<forall>y. y \<in> X \<longrightarrow>
          Real_Vector_Spaces.norm (y - c) \<le> R) \<and>
        slp_ae_bounded_measurable lborel M multiplier
        \<longrightarrow>
        slp_ae_bounded_measurable lborel ((1 / 2) * M)
          (slp_restrict_field X
            (slp_right_neumann_step tau c cutoff coefficient multiplier)))"
proof -
  obtain T :: real where T_lower: "2 \<le> T"
    and contraction:
      "\<forall>tau c multiplier M.
        T \<le> tau \<and>
        (\<forall>y. y \<in> X \<longrightarrow>
          Real_Vector_Spaces.norm (y - c) \<le> R) \<and>
        multiplier \<in> borel_measurable lborel \<and>
        (AE x in lborel. norm (multiplier x) \<le> M) \<and>
        0 \<le> M
        \<longrightarrow>
        (\<lambda>z :: slp_point.
          ereal (Real_Vector_Spaces.norm
            (slp_restrict_field X
              (slp_right_neumann_step tau c cutoff coefficient multiplier) z)))
          \<in> borel_measurable (lborel :: slp_point measure)
        \<and>
        esssup (lborel :: slp_point measure)
          (\<lambda>z :: slp_point.
            ereal (Real_Vector_Spaces.norm
              (slp_restrict_field X
                (slp_right_neumann_step tau c cutoff coefficient multiplier) z)))
          \<le> ereal ((1 / 2) * M)"
    using slp_nested_coefficient_product_right_esssup_contraction[
        OF riesz_hls cauchy_test_left_inverse evans_density
          exponent_lower exponent_upper loss_positive loss_upper
          radius_nonnegative radius_lower set_radius X_open X_bounded
          X_bounded cutoff_test cutoff_bound cutoff_derivative_zero_bound
          cutoff_derivative_one_bound A0_nonnegative B0_nonnegative
          B1_nonnegative coefficient_lp coefficient_support]
    unfolding slp_right_neumann_step_def
    by blast

  obtain C :: real where C_positive: "0 < C"
    and two_cauchy:
      "\<forall>tau1 tau2 c1 c2 f outer inner.
        aim_complex_lp_on_plane p f \<longrightarrow>
        slp_cauchy_transform outer
          (slp_oscillatory_modulation tau1 c1
            (\<lambda>y. cutoff y * slp_cauchy_transform inner
              (slp_oscillatory_modulation tau2 c2 f) y))
          \<in> borel_measurable lborel
        \<and>
        (\<forall>z\<in>X.
          slp_cauchy_integrable_at outer
            (slp_oscillatory_modulation tau1 c1
              (\<lambda>y. cutoff y * slp_cauchy_transform inner
                (slp_oscillatory_modulation tau2 c2 f) y)) z
          \<and>
          Real_Vector_Spaces.norm
            (slp_cauchy_transform outer
              (slp_oscillatory_modulation tau1 c1
                (\<lambda>y. cutoff y * slp_cauchy_transform inner
                  (slp_oscillatory_modulation tau2 c2 f) y)) z)
            \<le> C * aim_complex_lp_norm p f)"
    using slp_two_oscillatory_cauchy_test_cutoff_bound[
        OF exponent_lower exponent_upper X_bounded cutoff_test]
    by blast

  have X_measurable: "X \<in> sets lborel"
    using X_open by simp
  have p_positive: "0 < p"
    using exponent_lower by linarith

  show ?thesis
  proof (rule exI[of _ T], rule conjI[OF T_lower])
    show
      "\<forall>tau c multiplier M.
        T \<le> tau \<and>
        (\<forall>y. y \<in> X \<longrightarrow>
          Real_Vector_Spaces.norm (y - c) \<le> R) \<and>
        slp_ae_bounded_measurable lborel M multiplier
        \<longrightarrow>
        slp_ae_bounded_measurable lborel ((1 / 2) * M)
          (slp_restrict_field X
            (slp_right_neumann_step tau c cutoff coefficient multiplier))"
    proof (intro allI impI)
      fix tau :: real and c :: slp_point
        and multiplier :: slp_scalar_field and M :: real
      assume input:
        "T \<le> tau \<and>
          (\<forall>y. y \<in> X \<longrightarrow>
            Real_Vector_Spaces.norm (y - c) \<le> R) \<and>
          slp_ae_bounded_measurable lborel M multiplier"
      then have tau_lower: "T \<le> tau"
        and center_geometry:
          "\<forall>y. y \<in> X \<longrightarrow>
            Real_Vector_Spaces.norm (y - c) \<le> R"
        and multiplier_admissible:
          "slp_ae_bounded_measurable lborel M multiplier"
        by blast+
      have M_nonnegative: "0 \<le> M"
        and multiplier_measurable:
          "multiplier \<in> borel_measurable lborel"
        and multiplier_bound:
          "AE x in lborel. norm (multiplier x) \<le> M"
        using multiplier_admissible
        unfolding slp_ae_bounded_measurable_def by blast+

      have product_lp:
          "aim_complex_lp_on_plane p
            (\<lambda>x. multiplier x * coefficient x)"
        by (rule slp_complex_lp_AE_bounded_multiplier(1)[
              OF p_positive multiplier_measurable multiplier_bound
                M_nonnegative coefficient_lp])
      have source_lp:
          "aim_complex_lp_on_plane p
            (\<lambda>x. coefficient x * multiplier x)"
        using product_lp by (simp only: mult.commute)
      have step_measurable:
          "slp_right_neumann_step tau c cutoff coefficient multiplier
            \<in> borel_measurable lborel"
        using two_cauchy source_lp
        by (simp only: slp_right_neumann_step_def
            slp_partial_psi_inverse_def slp_dbar_psi_inverse_def; blast)
      have restricted_measurable:
          "slp_restrict_field X
              (slp_right_neumann_step tau c cutoff coefficient multiplier)
            \<in> borel_measurable lborel"
        by (rule slp_restrict_field_measurable[
              OF X_measurable step_measurable])

      have contraction_data:
          "(\<lambda>z :: slp_point.
            ereal (Real_Vector_Spaces.norm
              (slp_restrict_field X
                (slp_right_neumann_step tau c cutoff coefficient multiplier) z)))
            \<in> borel_measurable (lborel :: slp_point measure)
          \<and>
          esssup (lborel :: slp_point measure)
            (\<lambda>z :: slp_point.
              ereal (Real_Vector_Spaces.norm
                (slp_restrict_field X
                  (slp_right_neumann_step tau c cutoff coefficient multiplier) z)))
            \<le> ereal ((1 / 2) * M)"
        using contraction tau_lower center_geometry multiplier_measurable
          multiplier_bound M_nonnegative by blast
      have output_AE:
          "AE z in lborel.
            Real_Vector_Spaces.norm
              (slp_restrict_field X
                (slp_right_neumann_step tau c cutoff coefficient multiplier) z)
              \<le> (1 / 2) * M"
        by (rule slp_ereal_norm_esssup_bound_imp_AE[
              OF conjunct1[OF contraction_data]
                conjunct2[OF contraction_data]])
      have output_bound_nonnegative: "0 \<le> (1 / 2) * M"
        using M_nonnegative by simp
      show
        "slp_ae_bounded_measurable lborel ((1 / 2) * M)
          (slp_restrict_field X
            (slp_right_neumann_step tau c cutoff coefficient multiplier))"
        unfolding slp_ae_bounded_measurable_def
        using output_bound_nonnegative restricted_measurable output_AE
        by blast
    qed
  qed
qed

end

end
