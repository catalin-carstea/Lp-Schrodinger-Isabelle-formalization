theory Inverse_Schrodinger_Lp_Left_Neumann_Series_Fixed_Point
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_015.Inverse_Schrodinger_Lp_Left_Neumann_Series_Esssup_Convergence"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_015.Inverse_Schrodinger_Lp_Left_Neumann_Step_Difference"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Literal left Neumann series as an almost-everywhere fixed point\<close>

context slp_cauchy_local_w1s
begin

lemma slp_left_neumann_step_restrict_input:
  fixes X :: "slp_point set"
    and cutoff coefficient f :: slp_scalar_field
  assumes coefficient_support: "{x. coefficient x \<noteq> 0} \<subseteq> X"
  shows
    "slp_left_neumann_step tau c cutoff coefficient f =
      slp_left_neumann_step tau c cutoff coefficient
        (slp_restrict_field X f)"
proof -
  have source_restrict:
      "(\<lambda>y. coefficient y * f y) =
        (\<lambda>y. coefficient y * slp_restrict_field X f y)"
  proof (rule ext)
    fix y :: slp_point
    show "coefficient y * f y =
        coefficient y * slp_restrict_field X f y"
    proof (cases "y \<in> X")
      case True
      then show ?thesis
        by (simp add: slp_restrict_field_def)
    next
      case False
      then have coefficient_zero: "coefficient y = 0"
        using coefficient_support by auto
      then show ?thesis by simp
    qed
  qed
  show ?thesis
    unfolding slp_left_neumann_step_def
    by (subst source_restrict) (rule refl)
qed

theorem slp_left_neumann_series_fixed_point:
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
        slp_restrict_field X
            (slp_left_neumann_step tau c cutoff coefficient
              (slp_left_neumann_series_sum X tau c cutoff coefficient))
          \<in> borel_measurable lborel
        \<and>
        (AE z in lborel.
          summable (\<lambda>j.
            slp_restrict_field X
              (slp_left_neumann_step tau c cutoff coefficient
                (slp_restrict_field X
                  (slp_neumann_iterate
                    (slp_left_neumann_step tau c cutoff coefficient)
                    (slp_left_neumann_base tau c cutoff coefficient
                      SLP_Dbar_Inverse) j))) z))
        \<and>
        (AE z in lborel.
          slp_restrict_field X
              (slp_left_neumann_step tau c cutoff coefficient
                (slp_left_neumann_series_sum X tau c cutoff coefficient)) z =
            (\<Sum>j.
              slp_restrict_field X
                (slp_left_neumann_step tau c cutoff coefficient
                  (slp_restrict_field X
                    (slp_neumann_iterate
                      (slp_left_neumann_step tau c cutoff coefficient)
                      (slp_left_neumann_base tau c cutoff coefficient
                        SLP_Dbar_Inverse) j))) z))
        \<and>
        (AE z in lborel.
          slp_left_neumann_series_sum X tau c cutoff coefficient z =
            slp_restrict_field X
              (slp_left_neumann_base tau c cutoff coefficient
                SLP_Dbar_Inverse) z +
            slp_restrict_field X
              (slp_left_neumann_step tau c cutoff coefficient
                (slp_left_neumann_series_sum X tau c cutoff coefficient)) z))"
proof -
  obtain C CV TI :: real where C_positive: "0 < C"
    and CV_positive: "0 < CV"
    and iterate_threshold_lower: "2 \<le> TI"
    and iterate_data:
      "\<forall>tau c.
        TI \<le> tau \<and>
        (\<forall>y. y \<in> X \<longrightarrow>
          Real_Vector_Spaces.norm (y - c) \<le> R)
        \<longrightarrow>
        CV * tau powr (-(1 - 1 / p) + epsilon) \<le> 1 / 2
        \<and>
        (\<forall>j.
          slp_restrict_field X
              (slp_neumann_iterate
                (slp_left_neumann_step tau c cutoff coefficient)
                (slp_left_neumann_base tau c cutoff coefficient
                  SLP_Dbar_Inverse) j)
            \<in> borel_measurable lborel
          \<and>
          (\<lambda>z :: slp_point.
            ereal (Real_Vector_Spaces.norm
              (slp_restrict_field X
                (slp_neumann_iterate
                  (slp_left_neumann_step tau c cutoff coefficient)
                  (slp_left_neumann_base tau c cutoff coefficient
                    SLP_Dbar_Inverse) j) z)))
            \<in> borel_measurable (lborel :: slp_point measure)
          \<and>
          esssup (lborel :: slp_point measure)
            (\<lambda>z :: slp_point.
              ereal (Real_Vector_Spaces.norm
                (slp_restrict_field X
                  (slp_neumann_iterate
                    (slp_left_neumann_step tau c cutoff coefficient)
                    (slp_left_neumann_base tau c cutoff coefficient
                      SLP_Dbar_Inverse) j) z)))
            \<le> ereal
              (C * tau powr (-(1 - 1 / p) + epsilon) *
                (aim_complex_lp_norm p coefficient +
                  Real_Vector_Spaces.norm
                    (slp_dbar_inverse coefficient c)) *
                (CV * tau powr (-(1 - 1 / p) + epsilon)) ^ j)
          \<and>
          (AE z in lborel.
            Real_Vector_Spaces.norm
              (slp_restrict_field X
                (slp_neumann_iterate
                  (slp_left_neumann_step tau c cutoff coefficient)
                  (slp_left_neumann_base tau c cutoff coefficient
                    SLP_Dbar_Inverse) j) z)
              \<le> C * tau powr (-(1 - 1 / p) + epsilon) *
                (aim_complex_lp_norm p coefficient +
                  Real_Vector_Spaces.norm
                    (slp_dbar_inverse coefficient c)) *
                (CV * tau powr (-(1 - 1 / p) + epsilon)) ^ j)
          \<and>
          slp_complex_lp_on (aim_hls_target_exponent p) X
            (slp_neumann_iterate
              (slp_left_neumann_step tau c cutoff coefficient)
              (slp_left_neumann_base tau c cutoff coefficient
                SLP_Dbar_Inverse) j)
          \<and>
          slp_complex_lp_norm_on (aim_hls_target_exponent p) X
            (slp_neumann_iterate
              (slp_left_neumann_step tau c cutoff coefficient)
              (slp_left_neumann_base tau c cutoff coefficient
                SLP_Dbar_Inverse) j)
            \<le> C * inverse (sqrt tau) *
              (aim_complex_lp_norm p coefficient +
                Real_Vector_Spaces.norm
                  (slp_dbar_inverse coefficient c)) *
              (CV * tau powr (-(1 - 1 / p) + epsilon)) ^ j)"
    using slp_left_neumann_iterate_lpstar_geometric[
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

  let ?T = "max TI TS"
  show ?thesis
  proof (rule exI[of _ ?T], rule conjI)
    show "2 \<le> ?T"
      using iterate_threshold_lower by simp
  next
    show
      "\<forall>tau c.
        ?T \<le> tau \<and>
        (\<forall>y. y \<in> X \<longrightarrow>
          Real_Vector_Spaces.norm (y - c) \<le> R)
        \<longrightarrow>
        slp_restrict_field X
            (slp_left_neumann_step tau c cutoff coefficient
              (slp_left_neumann_series_sum X tau c cutoff coefficient))
          \<in> borel_measurable lborel
        \<and>
        (AE z in lborel.
          summable (\<lambda>j.
            slp_restrict_field X
              (slp_left_neumann_step tau c cutoff coefficient
                (slp_restrict_field X
                  (slp_neumann_iterate
                    (slp_left_neumann_step tau c cutoff coefficient)
                    (slp_left_neumann_base tau c cutoff coefficient
                      SLP_Dbar_Inverse) j))) z))
        \<and>
        (AE z in lborel.
          slp_restrict_field X
              (slp_left_neumann_step tau c cutoff coefficient
                (slp_left_neumann_series_sum X tau c cutoff coefficient)) z =
            (\<Sum>j.
              slp_restrict_field X
                (slp_left_neumann_step tau c cutoff coefficient
                  (slp_restrict_field X
                    (slp_neumann_iterate
                      (slp_left_neumann_step tau c cutoff coefficient)
                      (slp_left_neumann_base tau c cutoff coefficient
                        SLP_Dbar_Inverse) j))) z))
        \<and>
        (AE z in lborel.
          slp_left_neumann_series_sum X tau c cutoff coefficient z =
            slp_restrict_field X
              (slp_left_neumann_base tau c cutoff coefficient
                SLP_Dbar_Inverse) z +
            slp_restrict_field X
              (slp_left_neumann_step tau c cutoff coefficient
                (slp_left_neumann_series_sum X tau c cutoff coefficient)) z)"
    proof (intro allI impI)
      fix tau :: real and c :: slp_point
      assume admissible:
        "?T \<le> tau \<and>
          (\<forall>y. y \<in> X \<longrightarrow>
            Real_Vector_Spaces.norm (y - c) \<le> R)"
      then have iterate_tau: "TI \<le> tau"
        and step_tau: "TS \<le> tau"
        and center_geometry:
          "\<forall>y. y \<in> X \<longrightarrow>
            Real_Vector_Spaces.norm (y - c) \<le> R"
        by auto

      let ?rho = "CV * tau powr (-(1 - 1 / p) + epsilon)"
      let ?P =
        "C * tau powr (-(1 - 1 / p) + epsilon) *
          (aim_complex_lp_norm p coefficient +
            Real_Vector_Spaces.norm (slp_dbar_inverse coefficient c))"
      let ?U =
        "\<lambda>j. slp_restrict_field X
          (slp_neumann_iterate
            (slp_left_neumann_step tau c cutoff coefficient)
            (slp_left_neumann_base tau c cutoff coefficient
              SLP_Dbar_Inverse) j)"
      let ?S =
        "\<lambda>f. slp_restrict_field X
          (slp_left_neumann_step tau c cutoff coefficient f)"
      let ?W =
        "slp_left_neumann_series_sum X tau c cutoff coefficient"

      have at_tau:
          "?rho \<le> 1 / 2 \<and> (\<forall>j.
            ?U j \<in> borel_measurable lborel
            \<and>
            (\<lambda>z :: slp_point.
              ereal (Real_Vector_Spaces.norm (?U j z)))
              \<in> borel_measurable (lborel :: slp_point measure)
            \<and>
            esssup (lborel :: slp_point measure)
              (\<lambda>z :: slp_point.
                ereal (Real_Vector_Spaces.norm (?U j z)))
              \<le> ereal (?P * ?rho ^ j)
            \<and>
            (AE z in lborel.
              Real_Vector_Spaces.norm (?U j z) \<le> ?P * ?rho ^ j)
            \<and>
            slp_complex_lp_on (aim_hls_target_exponent p) X
              (slp_neumann_iterate
                (slp_left_neumann_step tau c cutoff coefficient)
                (slp_left_neumann_base tau c cutoff coefficient
                  SLP_Dbar_Inverse) j)
            \<and>
            slp_complex_lp_norm_on (aim_hls_target_exponent p) X
              (slp_neumann_iterate
                (slp_left_neumann_step tau c cutoff coefficient)
                (slp_left_neumann_base tau c cutoff coefficient
                  SLP_Dbar_Inverse) j)
              \<le> C * inverse (sqrt tau) *
                (aim_complex_lp_norm p coefficient +
                  Real_Vector_Spaces.norm
                    (slp_dbar_inverse coefficient c)) * ?rho ^ j)"
        using iterate_data iterate_tau center_geometry by blast
      have rho_half: "?rho \<le> 1 / 2"
        using at_tau by blast
      have rho_nonnegative: "0 \<le> ?rho"
        by (rule mult_nonneg_nonneg)
          (use CV_positive in linarith, rule powr_ge_zero)
      have rho_strict: "?rho < 1"
        using rho_half by linarith
      have coefficient_norm_nonnegative:
          "0 \<le> aim_complex_lp_norm p coefficient"
        unfolding aim_complex_lp_norm_def by (rule powr_ge_zero)
      have datum_nonnegative:
          "0 \<le> aim_complex_lp_norm p coefficient +
            Real_Vector_Spaces.norm (slp_dbar_inverse coefficient c)"
        using coefficient_norm_nonnegative by simp
      have P_nonnegative: "0 \<le> ?P"
      proof (rule mult_nonneg_nonneg)
        show "0 \<le> C * tau powr (-(1 - 1 / p) + epsilon)"
          by (rule mult_nonneg_nonneg)
            (use C_positive in linarith, rule powr_ge_zero)
        show "0 \<le> aim_complex_lp_norm p coefficient +
            Real_Vector_Spaces.norm (slp_dbar_inverse coefficient c)"
          by (rule datum_nonnegative)
      qed
      have terms_measurable:
          "\<And>j. ?U j \<in> borel_measurable lborel"
        using at_tau by blast
      have term_bound:
          "\<And>j. AE z in lborel.
            Real_Vector_Spaces.norm (?U j z) \<le> ?P * ?rho ^ j"
        using at_tau by blast

      have recurrence:
          "\<And>j. AE z in lborel. ?U (Suc j) z = ?S (?U j) z"
      proof -
        fix j :: nat
        have recurrence_eq: "?U (Suc j) = ?S (?U j)"
          unfolding slp_neumann_iterate_Suc
          apply (subst slp_left_neumann_step_restrict_input[
            OF coefficient_support])
          apply (rule refl)
          done
        show "AE z in lborel. ?U (Suc j) z = ?S (?U j) z"
          using recurrence_eq by simp
      qed

      have operator_at_tau:
          "\<And>K f. slp_ae_bounded_measurable lborel K f \<Longrightarrow>
            slp_ae_bounded_measurable lborel ((1 / 2) * K) (?S f)"
        using step_data step_tau center_geometry by blast
      have operator_closed:
          "\<And>K f. slp_ae_bounded_measurable lborel K f \<Longrightarrow>
            ?S f \<in> borel_measurable lborel"
        using operator_at_tau
        unfolding slp_ae_bounded_measurable_def by blast
      have operator_contraction:
          "\<And>K f. slp_ae_bounded_measurable lborel K f \<Longrightarrow>
            AE z in lborel. Real_Vector_Spaces.norm (?S f z) \<le> (1 / 2) * K"
        using operator_at_tau
        unfolding slp_ae_bounded_measurable_def by blast
      have operator_difference:
          "\<And>K L f g.
            slp_ae_bounded_measurable lborel K f \<Longrightarrow>
            slp_ae_bounded_measurable lborel L g \<Longrightarrow>
            AE z in lborel.
              ?S (\<lambda>y. f y - g y) z = ?S f z - ?S g z"
      proof -
        fix K L :: real and f g :: slp_scalar_field
        assume first_admissible: "slp_ae_bounded_measurable lborel K f"
          and second_admissible: "slp_ae_bounded_measurable lborel L g"
        have difference_eq:
            "?S (\<lambda>y. f y - g y) =
              (\<lambda>z. ?S f z - ?S g z)"
          by (rule slp_left_neumann_step_restricted_difference[
                OF riesz_hls exponent_lower exponent_upper X_bounded
                  cutoff_test coefficient_lp first_admissible
                  second_admissible])
        show "AE z in lborel.
            ?S (\<lambda>y. f y - g y) z = ?S f z - ?S g z"
          using difference_eq by simp
      qed
      have kappa_nonnegative: "0 \<le> (1 / 2 :: real)"
        by simp
      have kappa_strict: "(1 / 2 :: real) < 1"
        by simp
      note bridge = slp_ae_neumann_sum_fixed_point[
        where M = "(lborel :: slp_point measure)" and U = ?U and S = ?S
          and P = ?P and rho = ?rho and kappa = "1 / 2",
        OF terms_measurable P_nonnegative rho_nonnegative rho_strict
          term_bound recurrence kappa_nonnegative kappa_strict
          operator_closed operator_difference
          operator_contraction]
      have sum_image_measurable:
          "?S ?W \<in> borel_measurable lborel"
        using bridge(1)
        unfolding slp_left_neumann_series_sum_def .
      have image_series_summable:
          "AE z in lborel. summable (\<lambda>j. ?S (?U j) z)"
        using bridge(2)
        unfolding slp_left_neumann_series_sum_def .
      have image_transports_sum:
          "AE z in lborel. ?S ?W z = (\<Sum>j. ?S (?U j) z)"
        using bridge(3)
        unfolding slp_left_neumann_series_sum_def .
      have literal_fixed_point:
          "AE z in lborel. ?W z =
            slp_restrict_field X
              (slp_left_neumann_base tau c cutoff coefficient
                SLP_Dbar_Inverse) z + ?S ?W z"
        using bridge(4)
        by (simp only: slp_left_neumann_series_sum_def
            slp_neumann_iterate_zero)
      have transport_and_fixed:
          "(AE z in lborel. ?S ?W z = (\<Sum>j. ?S (?U j) z))
            \<and> (AE z in lborel. ?W z =
              slp_restrict_field X
                (slp_left_neumann_base tau c cutoff coefficient
                  SLP_Dbar_Inverse) z + ?S ?W z)"
        by (rule conjI[OF image_transports_sum literal_fixed_point])
      have series_transport_and_fixed:
          "(AE z in lborel. summable (\<lambda>j. ?S (?U j) z))
            \<and> (AE z in lborel. ?S ?W z = (\<Sum>j. ?S (?U j) z))
            \<and> (AE z in lborel. ?W z =
              slp_restrict_field X
                (slp_left_neumann_base tau c cutoff coefficient
                  SLP_Dbar_Inverse) z + ?S ?W z)"
        by (rule conjI[OF image_series_summable transport_and_fixed])
      have all_results:
          "?S ?W \<in> borel_measurable lborel
            \<and> (AE z in lborel. summable (\<lambda>j. ?S (?U j) z))
            \<and> (AE z in lborel. ?S ?W z = (\<Sum>j. ?S (?U j) z))
            \<and> (AE z in lborel. ?W z =
              slp_restrict_field X
                (slp_left_neumann_base tau c cutoff coefficient
                  SLP_Dbar_Inverse) z + ?S ?W z)"
        by (rule conjI[OF sum_image_measurable
              series_transport_and_fixed])
      show
        "?S ?W \<in> borel_measurable lborel
          \<and> (AE z in lborel. summable (\<lambda>j. ?S (?U j) z))
          \<and> (AE z in lborel. ?S ?W z = (\<Sum>j. ?S (?U j) z))
          \<and> (AE z in lborel. ?W z =
            slp_restrict_field X
              (slp_left_neumann_base tau c cutoff coefficient
                SLP_Dbar_Inverse) z + ?S ?W z)"
        by (rule all_results)
    qed
  qed
qed

end

end
