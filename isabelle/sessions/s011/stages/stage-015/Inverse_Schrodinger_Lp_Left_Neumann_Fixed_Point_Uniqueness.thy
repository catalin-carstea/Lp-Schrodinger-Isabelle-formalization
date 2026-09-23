theory Inverse_Schrodinger_Lp_Left_Neumann_Fixed_Point_Uniqueness
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_015.Inverse_Schrodinger_Lp_AE_Fixed_Point_Uniqueness"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_015.Inverse_Schrodinger_Lp_Left_Neumann_Series_Fixed_Point"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Uniqueness of the literal restricted left Neumann fixed point\<close>

context slp_cauchy_local_w1s
begin

lemma slp_left_neumann_series_ae_bounded:
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
      (\<forall>tau c.
        T \<le> tau \<and>
        (\<forall>y. y \<in> X \<longrightarrow>
          Real_Vector_Spaces.norm (y - c) \<le> R)
        \<longrightarrow>
        (\<exists>K::real. slp_ae_bounded_measurable lborel K
          (slp_left_neumann_series_sum X tau c cutoff coefficient)))"
proof -
  obtain C CV T :: real where C_positive: "0 < C"
    and CV_positive: "0 < CV"
    and threshold_lower: "2 \<le> T"
    and series_data:
      "(\<forall>tau c.
        T \<le> tau \<and>
        (\<forall>y. y \<in> X \<longrightarrow>
          Real_Vector_Spaces.norm (y - c) \<le> R)
        \<longrightarrow>
        CV * tau powr (-(1 - 1 / p) + epsilon) \<le> 1 / 2
        \<and>
        slp_left_neumann_series_sum X tau c cutoff coefficient
          \<in> borel_measurable lborel
        \<and>
        (AE z in lborel.
          summable (\<lambda>j.
            Real_Vector_Spaces.norm
              (slp_restrict_field X
                (slp_neumann_iterate
                  (slp_left_neumann_step tau c cutoff coefficient)
                  (slp_left_neumann_base tau c cutoff coefficient
                    SLP_Dbar_Inverse) j) z)))
        \<and>
        (AE z in lborel.
          summable (\<lambda>j.
            slp_restrict_field X
              (slp_neumann_iterate
                (slp_left_neumann_step tau c cutoff coefficient)
                (slp_left_neumann_base tau c cutoff coefficient
                  SLP_Dbar_Inverse) j) z))
        \<and>
        (\<forall>N.
          esssup (lborel :: slp_point measure)
            (\<lambda>z :: slp_point.
              ereal (Real_Vector_Spaces.norm
                (slp_left_neumann_series_sum X tau c cutoff coefficient z -
                  (\<Sum>j<N.
                    slp_restrict_field X
                      (slp_neumann_iterate
                        (slp_left_neumann_step tau c cutoff coefficient)
                        (slp_left_neumann_base tau c cutoff coefficient
                          SLP_Dbar_Inverse) j) z))))
          \<le> ereal
            ((C * tau powr (-(1 - 1 / p) + epsilon) *
                (aim_complex_lp_norm p coefficient +
                  Real_Vector_Spaces.norm
                    (slp_dbar_inverse coefficient c))) *
              (CV * tau powr (-(1 - 1 / p) + epsilon)) ^ N /
              (1 -
                CV * tau powr (-(1 - 1 / p) + epsilon)))))"
    using slp_left_neumann_series_esssup_convergence[
      OF riesz_hls cauchy_test_left_inverse evans_density
        exponent_lower exponent_upper loss_positive loss_upper
        radius_nonnegative radius_lower set_radius X_open X_bounded cutoff_test
        cutoff_bound cutoff_derivative_zero_bound
        cutoff_derivative_one_bound A0_nonnegative B0_nonnegative
        B1_nonnegative coefficient_lp coefficient_support]
    by blast

  show ?thesis
  proof (rule exI[of _ T], rule conjI[OF threshold_lower])
    show
      "\<forall>tau c.
        T \<le> tau \<and>
        (\<forall>y. y \<in> X \<longrightarrow>
          Real_Vector_Spaces.norm (y - c) \<le> R)
        \<longrightarrow>
        (\<exists>K::real. slp_ae_bounded_measurable lborel K
          (slp_left_neumann_series_sum X tau c cutoff coefficient))"
    proof (intro allI impI)
      fix tau :: real and c :: slp_point
      assume admissible:
        "T \<le> tau \<and>
          (\<forall>y. y \<in> X \<longrightarrow>
            Real_Vector_Spaces.norm (y - c) \<le> R)"
      let ?rho = "CV * tau powr (-(1 - 1 / p) + epsilon)"
      let ?P =
        "C * tau powr (-(1 - 1 / p) + epsilon) *
          (aim_complex_lp_norm p coefficient +
            Real_Vector_Spaces.norm (slp_dbar_inverse coefficient c))"
      let ?W =
        "slp_left_neumann_series_sum X tau c cutoff coefficient"
      have at_tau:
          "?rho \<le> 1 / 2
            \<and> ?W \<in> borel_measurable lborel
            \<and> (\<forall>N.
              esssup (lborel :: slp_point measure)
                (\<lambda>z :: slp_point.
                  ereal (Real_Vector_Spaces.norm
                    (?W z -
                      (\<Sum>j<N. slp_restrict_field X
                        (slp_neumann_iterate
                          (slp_left_neumann_step tau c cutoff coefficient)
                          (slp_left_neumann_base tau c cutoff coefficient
                            SLP_Dbar_Inverse) j) z))))
                \<le> ereal (?P * ?rho ^ N / (1 - ?rho)))"
        using series_data admissible by blast
      have rho_half: "?rho \<le> 1 / 2"
        using at_tau by blast
      have W_measurable: "?W \<in> borel_measurable lborel"
        using at_tau by blast
      have all_tail_bounds:
          "\<forall>N.
            esssup (lborel :: slp_point measure)
              (\<lambda>z :: slp_point.
                ereal (Real_Vector_Spaces.norm
                  (?W z -
                    (\<Sum>j<N. slp_restrict_field X
                      (slp_neumann_iterate
                        (slp_left_neumann_step tau c cutoff coefficient)
                        (slp_left_neumann_base tau c cutoff coefficient
                          SLP_Dbar_Inverse) j) z))))
              \<le> ereal (?P * ?rho ^ N / (1 - ?rho))"
        using at_tau by blast
      have W_esssup:
          "esssup (lborel :: slp_point measure)
            (\<lambda>z :: slp_point.
              ereal (Real_Vector_Spaces.norm (?W z)))
            \<le> ereal (?P / (1 - ?rho))"
        using all_tail_bounds[rule_format, of 0] by simp
      have rho_nonnegative: "0 \<le> ?rho"
        by (rule mult_nonneg_nonneg)
          (use CV_positive in linarith, rule powr_ge_zero)
      have denominator_positive: "0 < 1 - ?rho"
        using rho_half by linarith
      have coefficient_norm_nonnegative:
          "0 \<le> aim_complex_lp_norm p coefficient"
        unfolding aim_complex_lp_norm_def by (rule powr_ge_zero)
      have datum_nonnegative:
          "0 \<le> aim_complex_lp_norm p coefficient +
            Real_Vector_Spaces.norm (slp_dbar_inverse coefficient c)"
        using coefficient_norm_nonnegative by simp
      have P_nonnegative: "0 \<le> ?P"
        by (intro mult_nonneg_nonneg)
          (use C_positive in linarith, rule powr_ge_zero,
            rule datum_nonnegative)
      have bound_nonnegative: "0 \<le> ?P / (1 - ?rho)"
        using P_nonnegative denominator_positive by simp
      have W_norm_measurable:
          "(\<lambda>z :: slp_point.
            ereal (Real_Vector_Spaces.norm (?W z)))
            \<in> borel_measurable (lborel :: slp_point measure)"
        using W_measurable by measurable
      have W_AE:
          "AE z in lborel.
            Real_Vector_Spaces.norm (?W z) \<le> ?P / (1 - ?rho)"
        by (rule slp_ereal_norm_esssup_bound_imp_AE[
              OF W_norm_measurable W_esssup])
      have W_admissible:
          "slp_ae_bounded_measurable lborel (?P / (1 - ?rho)) ?W"
        unfolding slp_ae_bounded_measurable_def
        using bound_nonnegative W_measurable W_AE by blast
      show
        "\<exists>K::real. slp_ae_bounded_measurable lborel K ?W"
        by (rule exI[of _ "?P / (1 - ?rho)"], rule W_admissible)
    qed
  qed
qed

theorem slp_left_neumann_series_fixed_point_unique:
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
      (\<forall>tau c candidate K.
        T \<le> tau \<and>
        (\<forall>y. y \<in> X \<longrightarrow>
          Real_Vector_Spaces.norm (y - c) \<le> R)
        \<and> slp_ae_bounded_measurable lborel K candidate
        \<and> (AE z in lborel.
          candidate z =
            slp_restrict_field X
              (slp_left_neumann_base tau c cutoff coefficient
                SLP_Dbar_Inverse) z +
            slp_restrict_field X
              (slp_left_neumann_step tau c cutoff coefficient candidate) z)
        \<longrightarrow>
        (AE z in lborel.
          candidate z =
            slp_left_neumann_series_sum X tau c cutoff coefficient z))"
proof -
  obtain TB :: real where bounded_threshold_lower: "2 \<le> TB"
    and bounded_data:
      "\<forall>tau c.
        TB \<le> tau \<and>
        (\<forall>y. y \<in> X \<longrightarrow>
          Real_Vector_Spaces.norm (y - c) \<le> R)
        \<longrightarrow>
        (\<exists>K::real. slp_ae_bounded_measurable lborel K
          (slp_left_neumann_series_sum X tau c cutoff coefficient))"
    using slp_left_neumann_series_ae_bounded[
      OF riesz_hls cauchy_test_left_inverse evans_density
        exponent_lower exponent_upper loss_positive loss_upper
        radius_nonnegative radius_lower set_radius X_open X_bounded cutoff_test
        cutoff_bound cutoff_derivative_zero_bound
        cutoff_derivative_one_bound A0_nonnegative B0_nonnegative
        B1_nonnegative coefficient_lp coefficient_support]
    by blast

  obtain TF :: real where fixed_threshold_lower: "2 \<le> TF"
    and fixed_data:
      "\<forall>tau c.
        TF \<le> tau \<and>
        (\<forall>y. y \<in> X \<longrightarrow>
          Real_Vector_Spaces.norm (y - c) \<le> R)
        \<longrightarrow>
        (AE z in lborel.
          slp_left_neumann_series_sum X tau c cutoff coefficient z =
            slp_restrict_field X
              (slp_left_neumann_base tau c cutoff coefficient
                SLP_Dbar_Inverse) z +
            slp_restrict_field X
              (slp_left_neumann_step tau c cutoff coefficient
                (slp_left_neumann_series_sum X tau c cutoff coefficient)) z)"
    using slp_left_neumann_series_fixed_point[
      OF riesz_hls cauchy_test_left_inverse evans_density
        exponent_lower exponent_upper loss_positive loss_upper
        radius_nonnegative radius_lower set_radius X_open X_bounded cutoff_test
        cutoff_bound cutoff_derivative_zero_bound
        cutoff_derivative_one_bound A0_nonnegative B0_nonnegative
        B1_nonnegative coefficient_lp coefficient_support]
    by blast

  obtain TS :: real where step_threshold_lower: "2 \<le> TS"
    and step_data:
      "\<forall>tau c multiplier M.
        TS \<le> tau \<and>
        (\<forall>y. y \<in> X \<longrightarrow>
          Real_Vector_Spaces.norm (y - c) \<le> R) \<and>
        slp_ae_bounded_measurable lborel M multiplier
        \<longrightarrow>
        slp_ae_bounded_measurable lborel ((1 / 2) * M)
          (slp_restrict_field X
            (slp_left_neumann_step tau c cutoff coefficient multiplier))"
    using slp_left_neumann_step_restricted_ae_contraction[
      OF riesz_hls cauchy_test_left_inverse evans_density
        exponent_lower exponent_upper loss_positive loss_upper
        radius_nonnegative radius_lower set_radius X_open X_bounded cutoff_test
        cutoff_bound cutoff_derivative_zero_bound
        cutoff_derivative_one_bound A0_nonnegative B0_nonnegative
        B1_nonnegative coefficient_lp coefficient_support]
    by blast

  let ?T = "max TB (max TF TS)"
  show ?thesis
  proof (rule exI[of _ ?T], rule conjI)
    show "2 \<le> ?T"
      using bounded_threshold_lower by simp
  next
    show
      "\<forall>tau c candidate K.
        ?T \<le> tau \<and>
        (\<forall>y. y \<in> X \<longrightarrow>
          Real_Vector_Spaces.norm (y - c) \<le> R)
        \<and> slp_ae_bounded_measurable lborel K candidate
        \<and> (AE z in lborel.
          candidate z =
            slp_restrict_field X
              (slp_left_neumann_base tau c cutoff coefficient
                SLP_Dbar_Inverse) z +
            slp_restrict_field X
              (slp_left_neumann_step tau c cutoff coefficient candidate) z)
        \<longrightarrow>
        (AE z in lborel.
          candidate z =
            slp_left_neumann_series_sum X tau c cutoff coefficient z)"
    proof (intro allI impI)
      fix tau :: real and c :: slp_point
        and candidate :: slp_scalar_field and K :: real
      assume input:
        "?T \<le> tau \<and>
          (\<forall>y. y \<in> X \<longrightarrow>
            Real_Vector_Spaces.norm (y - c) \<le> R)
          \<and> slp_ae_bounded_measurable lborel K candidate
          \<and> (AE z in lborel.
            candidate z =
              slp_restrict_field X
                (slp_left_neumann_base tau c cutoff coefficient
                  SLP_Dbar_Inverse) z +
              slp_restrict_field X
                (slp_left_neumann_step tau c cutoff coefficient candidate) z)"
      then have bounded_tau: "TB \<le> tau"
        and fixed_tau: "TF \<le> tau"
        and step_tau: "TS \<le> tau"
        and center_geometry:
          "\<forall>y. y \<in> X \<longrightarrow>
            Real_Vector_Spaces.norm (y - c) \<le> R"
        and candidate_bound:
          "slp_ae_bounded_measurable lborel K candidate"
        and candidate_fixed:
          "AE z in lborel.
            candidate z =
              slp_restrict_field X
                (slp_left_neumann_base tau c cutoff coefficient
                  SLP_Dbar_Inverse) z +
              slp_restrict_field X
                (slp_left_neumann_step tau c cutoff coefficient candidate) z"
        by auto
      let ?W =
        "slp_left_neumann_series_sum X tau c cutoff coefficient"
      let ?B =
        "slp_restrict_field X
          (slp_left_neumann_base tau c cutoff coefficient SLP_Dbar_Inverse)"
      let ?S =
        "\<lambda>f. slp_restrict_field X
          (slp_left_neumann_step tau c cutoff coefficient f)"

      obtain L :: real where W_bound:
          "slp_ae_bounded_measurable lborel L ?W"
        using bounded_data bounded_tau center_geometry by blast
      have W_fixed: "AE z in lborel. ?W z = ?B z + ?S ?W z"
        using fixed_data fixed_tau center_geometry by blast
      have operator_at_tau:
          "\<And>J f. slp_ae_bounded_measurable lborel J f \<Longrightarrow>
            slp_ae_bounded_measurable lborel ((1 / 2) * J) (?S f)"
        using step_data step_tau center_geometry by blast
      have operator_contraction:
          "\<And>J f. slp_ae_bounded_measurable lborel J f \<Longrightarrow>
            AE z in lborel.
              Real_Vector_Spaces.norm (?S f z) \<le> (1 / 2) * J"
        using operator_at_tau
        unfolding slp_ae_bounded_measurable_def by blast
      have operator_difference:
          "\<And>J H f g.
            slp_ae_bounded_measurable lborel J f \<Longrightarrow>
            slp_ae_bounded_measurable lborel H g \<Longrightarrow>
            AE z in lborel.
              ?S (\<lambda>y. f y - g y) z = ?S f z - ?S g z"
      proof -
        fix J H :: real and f g :: slp_scalar_field
        assume f_bound: "slp_ae_bounded_measurable lborel J f"
          and g_bound: "slp_ae_bounded_measurable lborel H g"
        have difference_eq:
            "?S (\<lambda>y. f y - g y) =
              (\<lambda>z. ?S f z - ?S g z)"
          by (rule slp_left_neumann_step_restricted_difference[
                OF riesz_hls exponent_lower exponent_upper X_bounded
                  cutoff_test coefficient_lp f_bound g_bound])
        show "AE z in lborel.
            ?S (\<lambda>y. f y - g y) z = ?S f z - ?S g z"
          using difference_eq by simp
      qed
      have kappa_nonnegative: "0 \<le> (1 / 2 :: real)"
        by simp
      have kappa_strict: "(1 / 2 :: real) < 1"
        by simp
      show "AE z in lborel. candidate z = ?W z"
        by (rule slp_ae_affine_fixed_point_unique[
              where M = "(lborel :: slp_point measure)" and S = ?S and B = ?B
                and f = candidate and g = ?W and K = K and L = L
                and kappa = "1 / 2",
              OF candidate_bound W_bound candidate_fixed W_fixed
                kappa_nonnegative kappa_strict operator_difference
                operator_contraction])
    qed
  qed
qed

end

end
