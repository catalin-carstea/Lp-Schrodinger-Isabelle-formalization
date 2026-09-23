theory Inverse_Schrodinger_Lp_Right_Neumann_Series_Esssup_Convergence
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_015.Inverse_Schrodinger_Lp_Measurable_Geometric_Series_Esssup_Tail"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_016.Inverse_Schrodinger_Lp_Right_Neumann_Iterate_Lpstar_Geometric"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Literal right Neumann series in raw essential-supremum form\<close>

definition slp_right_neumann_series_sum ::
    "slp_point set \<Rightarrow> real \<Rightarrow> slp_point \<Rightarrow>
      slp_scalar_field \<Rightarrow> slp_scalar_field \<Rightarrow> slp_scalar_field"
  where
  "slp_right_neumann_series_sum X tau c cutoff coefficient =
    (\<lambda>z. \<Sum>j.
      slp_restrict_field X
        (slp_neumann_iterate
          (slp_right_neumann_step tau c cutoff coefficient)
          (slp_right_neumann_base tau c cutoff coefficient
            SLP_Partial_Inverse) j) z)"

context slp_cauchy_local_w1s
begin

theorem slp_right_neumann_series_esssup_convergence:
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
    "\<exists>C CV T::real. 0 < C \<and> 0 < CV \<and> 2 \<le> T \<and>
      (\<forall>tau c.
        T \<le> tau \<and>
        (\<forall>y. y \<in> X \<longrightarrow>
          Real_Vector_Spaces.norm (y - c) \<le> R)
        \<longrightarrow>
        CV * tau powr (-(1 - 1 / p) + epsilon) \<le> 1 / 2 \<and>
        slp_right_neumann_series_sum X tau c cutoff coefficient
          \<in> borel_measurable lborel
        \<and>
        (AE z in lborel.
          summable (\<lambda>j.
            Real_Vector_Spaces.norm
              (slp_restrict_field X
                (slp_neumann_iterate
                  (slp_right_neumann_step tau c cutoff coefficient)
                  (slp_right_neumann_base tau c cutoff coefficient
                    SLP_Partial_Inverse) j) z)))
        \<and>
        (AE z in lborel.
          summable (\<lambda>j.
            slp_restrict_field X
              (slp_neumann_iterate
                (slp_right_neumann_step tau c cutoff coefficient)
                (slp_right_neumann_base tau c cutoff coefficient
                  SLP_Partial_Inverse) j) z))
        \<and>
        (\<forall>N.
          esssup (lborel :: slp_point measure)
            (\<lambda>z :: slp_point.
              ereal (Real_Vector_Spaces.norm
                (slp_right_neumann_series_sum X tau c cutoff coefficient z -
                  (\<Sum>j<N.
                    slp_restrict_field X
                      (slp_neumann_iterate
                        (slp_right_neumann_step tau c cutoff coefficient)
                        (slp_right_neumann_base tau c cutoff coefficient
                          SLP_Partial_Inverse) j) z))))
          \<le> ereal
            ((C * tau powr (-(1 - 1 / p) + epsilon) *
                (aim_complex_lp_norm p coefficient +
                  Real_Vector_Spaces.norm
                    (slp_partial_inverse coefficient c))) *
              (CV * tau powr (-(1 - 1 / p) + epsilon)) ^ N /
              (1 -
                CV * tau powr (-(1 - 1 / p) + epsilon)))))"
proof -
  obtain C CV T :: real where C_positive: "0 < C"
    and CV_positive: "0 < CV"
    and threshold_lower: "2 \<le> T"
    and iterate_data:
      "\<forall>tau c.
        T \<le> tau \<and>
        (\<forall>y. y \<in> X \<longrightarrow>
          Real_Vector_Spaces.norm (y - c) \<le> R)
        \<longrightarrow>
        CV * tau powr (-(1 - 1 / p) + epsilon) \<le> 1 / 2 \<and>
        (\<forall>j.
          slp_restrict_field X
              (slp_neumann_iterate
                (slp_right_neumann_step tau c cutoff coefficient)
                (slp_right_neumann_base tau c cutoff coefficient
                  SLP_Partial_Inverse) j)
            \<in> borel_measurable lborel
          \<and>
          (\<lambda>z :: slp_point.
            ereal (Real_Vector_Spaces.norm
              (slp_restrict_field X
                (slp_neumann_iterate
                  (slp_right_neumann_step tau c cutoff coefficient)
                  (slp_right_neumann_base tau c cutoff coefficient
                    SLP_Partial_Inverse) j) z)))
            \<in> borel_measurable (lborel :: slp_point measure)
          \<and>
          esssup (lborel :: slp_point measure)
            (\<lambda>z :: slp_point.
              ereal (Real_Vector_Spaces.norm
                (slp_restrict_field X
                  (slp_neumann_iterate
                    (slp_right_neumann_step tau c cutoff coefficient)
                    (slp_right_neumann_base tau c cutoff coefficient
                      SLP_Partial_Inverse) j) z)))
            \<le> ereal
              (C * tau powr (-(1 - 1 / p) + epsilon) *
                (aim_complex_lp_norm p coefficient +
                  Real_Vector_Spaces.norm
                    (slp_partial_inverse coefficient c)) *
                (CV * tau powr (-(1 - 1 / p) + epsilon)) ^ j)
          \<and>
          (AE z in lborel.
            Real_Vector_Spaces.norm
              (slp_restrict_field X
                (slp_neumann_iterate
                  (slp_right_neumann_step tau c cutoff coefficient)
                  (slp_right_neumann_base tau c cutoff coefficient
                    SLP_Partial_Inverse) j) z)
              \<le> C * tau powr (-(1 - 1 / p) + epsilon) *
                (aim_complex_lp_norm p coefficient +
                  Real_Vector_Spaces.norm
                    (slp_partial_inverse coefficient c)) *
                (CV * tau powr (-(1 - 1 / p) + epsilon)) ^ j)
          \<and>
          slp_complex_lp_on (aim_hls_target_exponent p) X
            (slp_neumann_iterate
              (slp_right_neumann_step tau c cutoff coefficient)
              (slp_right_neumann_base tau c cutoff coefficient
                SLP_Partial_Inverse) j)
          \<and>
          slp_complex_lp_norm_on (aim_hls_target_exponent p) X
            (slp_neumann_iterate
              (slp_right_neumann_step tau c cutoff coefficient)
              (slp_right_neumann_base tau c cutoff coefficient
                SLP_Partial_Inverse) j)
            \<le> C * inverse (sqrt tau) *
              (aim_complex_lp_norm p coefficient +
                Real_Vector_Spaces.norm
                  (slp_partial_inverse coefficient c)) *
              (CV * tau powr (-(1 - 1 / p) + epsilon)) ^ j)"
    using slp_right_neumann_iterate_lpstar_geometric[
      OF riesz_hls cauchy_test_left_inverse evans_density
        exponent_lower exponent_upper loss_positive loss_upper
        radius_nonnegative radius_lower set_radius X_open X_bounded cutoff_test
        cutoff_bound cutoff_derivative_zero_bound
        cutoff_derivative_one_bound A0_nonnegative B0_nonnegative
        B1_nonnegative coefficient_lp coefficient_support]
    by blast

  show ?thesis
  proof (rule exI[of _ C], rule exI[of _ CV], rule exI[of _ T],
      rule conjI[OF C_positive], rule conjI[OF CV_positive],
      rule conjI[OF threshold_lower])
    show
      "\<forall>tau c.
        T \<le> tau \<and>
        (\<forall>y. y \<in> X \<longrightarrow>
          Real_Vector_Spaces.norm (y - c) \<le> R)
        \<longrightarrow>
        CV * tau powr (-(1 - 1 / p) + epsilon) \<le> 1 / 2 \<and>
        slp_right_neumann_series_sum X tau c cutoff coefficient
          \<in> borel_measurable lborel
        \<and>
        (AE z in lborel.
          summable (\<lambda>j.
            Real_Vector_Spaces.norm
              (slp_restrict_field X
                (slp_neumann_iterate
                  (slp_right_neumann_step tau c cutoff coefficient)
                  (slp_right_neumann_base tau c cutoff coefficient
                    SLP_Partial_Inverse) j) z)))
        \<and>
        (AE z in lborel.
          summable (\<lambda>j.
            slp_restrict_field X
              (slp_neumann_iterate
                (slp_right_neumann_step tau c cutoff coefficient)
                (slp_right_neumann_base tau c cutoff coefficient
                  SLP_Partial_Inverse) j) z))
        \<and>
        (\<forall>N.
          esssup (lborel :: slp_point measure)
            (\<lambda>z :: slp_point.
              ereal (Real_Vector_Spaces.norm
                (slp_right_neumann_series_sum X tau c cutoff coefficient z -
                  (\<Sum>j<N.
                    slp_restrict_field X
                      (slp_neumann_iterate
                        (slp_right_neumann_step tau c cutoff coefficient)
                        (slp_right_neumann_base tau c cutoff coefficient
                          SLP_Partial_Inverse) j) z))))
          \<le> ereal
            ((C * tau powr (-(1 - 1 / p) + epsilon) *
                (aim_complex_lp_norm p coefficient +
                  Real_Vector_Spaces.norm
                    (slp_partial_inverse coefficient c))) *
              (CV * tau powr (-(1 - 1 / p) + epsilon)) ^ N /
              (1 -
                CV * tau powr (-(1 - 1 / p) + epsilon))))"
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
            Real_Vector_Spaces.norm (slp_partial_inverse coefficient c))"
      let ?U =
        "\<lambda>j. slp_restrict_field X
          (slp_neumann_iterate
            (slp_right_neumann_step tau c cutoff coefficient)
            (slp_right_neumann_base tau c cutoff coefficient
              SLP_Partial_Inverse) j)"
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
                (slp_right_neumann_step tau c cutoff coefficient)
                (slp_right_neumann_base tau c cutoff coefficient
                  SLP_Partial_Inverse) j)
            \<and>
            slp_complex_lp_norm_on (aim_hls_target_exponent p) X
              (slp_neumann_iterate
                (slp_right_neumann_step tau c cutoff coefficient)
                (slp_right_neumann_base tau c cutoff coefficient
                  SLP_Partial_Inverse) j)
              \<le> C * inverse (sqrt tau) *
                (aim_complex_lp_norm p coefficient +
                  Real_Vector_Spaces.norm
                    (slp_partial_inverse coefficient c)) *
                ?rho ^ j)"
        using iterate_data[rule_format, OF admissible] .
      have rho_half: "?rho \<le> 1 / 2"
        using at_tau by blast
      have tau_lower: "2 \<le> tau"
        using threshold_lower admissible by linarith
      have tau_positive: "0 < tau"
        using tau_lower by linarith
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
            Real_Vector_Spaces.norm (slp_partial_inverse coefficient c)"
        using coefficient_norm_nonnegative by simp
      have P_nonnegative: "0 \<le> ?P"
      proof (rule mult_nonneg_nonneg)
        show "0 \<le> C * tau powr (-(1 - 1 / p) + epsilon)"
          by (rule mult_nonneg_nonneg)
            (use C_positive in linarith, rule powr_ge_zero)
        show "0 \<le> aim_complex_lp_norm p coefficient +
            Real_Vector_Spaces.norm (slp_partial_inverse coefficient c)"
          by (rule datum_nonnegative)
      qed
      have U_measurable: "\<And>j. ?U j \<in> borel_measurable lborel"
        using at_tau by blast
      have U_bound:
          "\<And>j. AE z in lborel.
            Real_Vector_Spaces.norm (?U j z) \<le> ?P * ?rho ^ j"
        using at_tau by blast
      note series =
        slp_measurable_geometric_series_esssup_tail[
          where M = "(lborel :: slp_point measure)" and U = ?U
            and P = ?P and rho = ?rho,
          OF U_measurable P_nonnegative rho_nonnegative rho_strict U_bound]
      have series_measurable:
          "slp_right_neumann_series_sum X tau c cutoff coefficient
            \<in> borel_measurable lborel"
        using series(1)
        unfolding slp_right_neumann_series_sum_def by simp
      have norm_summable:
          "AE z in lborel.
            summable (\<lambda>j. Real_Vector_Spaces.norm (?U j z))"
        by (rule series(2))
      have vector_summable:
          "AE z in lborel. summable (\<lambda>j. ?U j z)"
        by (rule series(3))
      have tail:
          "\<forall>N.
            esssup (lborel :: slp_point measure)
              (\<lambda>z :: slp_point.
                ereal (Real_Vector_Spaces.norm
                  (slp_right_neumann_series_sum X tau c cutoff coefficient z -
                    (\<Sum>j<N. ?U j z))))
            \<le> ereal (?P * ?rho ^ N / (1 - ?rho))"
      proof
        fix N :: nat
        show
          "esssup (lborel :: slp_point measure)
              (\<lambda>z :: slp_point.
                ereal (Real_Vector_Spaces.norm
                  (slp_right_neumann_series_sum X tau c cutoff coefficient z -
                    (\<Sum>j<N. ?U j z))))
            \<le> ereal (?P * ?rho ^ N / (1 - ?rho))"
          using series(4)[of N]
          unfolding slp_right_neumann_series_sum_def by simp
      qed
      show
        "?rho \<le> 1 / 2 \<and>
          slp_right_neumann_series_sum X tau c cutoff coefficient
            \<in> borel_measurable lborel
          \<and>
          (AE z in lborel.
            summable (\<lambda>j. Real_Vector_Spaces.norm (?U j z)))
          \<and>
          (AE z in lborel. summable (\<lambda>j. ?U j z))
          \<and>
          (\<forall>N.
            esssup (lborel :: slp_point measure)
              (\<lambda>z :: slp_point.
                ereal (Real_Vector_Spaces.norm
                  (slp_right_neumann_series_sum X tau c cutoff coefficient z -
                    (\<Sum>j<N. ?U j z))))
            \<le> ereal (?P * ?rho ^ N / (1 - ?rho)))"
        using rho_half series_measurable norm_summable vector_summable tail
        by blast
    qed
  qed
qed

end

end
