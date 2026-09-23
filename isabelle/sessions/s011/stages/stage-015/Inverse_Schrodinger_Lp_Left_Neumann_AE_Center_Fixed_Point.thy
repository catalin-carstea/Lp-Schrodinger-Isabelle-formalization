theory Inverse_Schrodinger_Lp_Left_Neumann_AE_Center_Fixed_Point
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_015.Inverse_Schrodinger_Lp_Left_Neumann_Fixed_Point_Uniqueness"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_015.Inverse_Schrodinger_Lp_Oscillatory_Cauchy_Difference_AE"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Almost-everywhere centers for the unique left Neumann fixed point\<close>

context slp_cauchy_local_w1s
begin

theorem slp_left_neumann_series_ae_center_fixed_point_unique:
  fixes p epsilon A R A0 B0 B1 :: real
    and Omega X :: "slp_point set"
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
    and center_geometry:
      "\<And>c y :: slp_point. c \<in> Omega \<Longrightarrow> y \<in> X \<Longrightarrow>
        Real_Vector_Spaces.norm (y - c) \<le> R"
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
      (AE c in (lborel :: slp_point measure).
        c \<in> Omega \<longrightarrow>
        slp_cauchy_integrable_at SLP_Dbar_Inverse coefficient c
        \<and> (\<forall>tau. T \<le> tau \<longrightarrow>
          (\<exists>K::real. slp_ae_bounded_measurable lborel K
            (slp_left_neumann_series_sum X tau c cutoff coefficient))
          \<and> (AE z in lborel.
            slp_left_neumann_series_sum X tau c cutoff coefficient z =
              slp_restrict_field X
                (slp_left_neumann_base tau c cutoff coefficient
                  SLP_Dbar_Inverse) z +
              slp_restrict_field X
                (slp_left_neumann_step tau c cutoff coefficient
                  (slp_left_neumann_series_sum X tau c cutoff coefficient)) z)
          \<and> (\<forall>candidate K.
            slp_ae_bounded_measurable lborel K candidate
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
                slp_left_neumann_series_sum X tau c cutoff coefficient z))))"
proof -
  interpret riesz: aim_planar_riesz_hls
    by unfold_locales (rule riesz_hls)

  have center_integrable:
      "AE c in (lborel :: slp_point measure).
        slp_cauchy_integrable_at SLP_Dbar_Inverse coefficient c"
    by (rule riesz.slp_cauchy_integrable_at_AE[
          OF exponent_lower exponent_upper coefficient_lp])

  obtain TB :: real where bounded_threshold: "2 \<le> TB"
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

  obtain TF :: real where fixed_threshold: "2 \<le> TF"
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

  obtain TU :: real where unique_threshold: "2 \<le> TU"
    and unique_data:
      "\<forall>tau c candidate K.
        TU \<le> tau \<and>
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
    using slp_left_neumann_series_fixed_point_unique[
      OF riesz_hls cauchy_test_left_inverse evans_density
        exponent_lower exponent_upper loss_positive loss_upper
        radius_nonnegative radius_lower set_radius X_open X_bounded cutoff_test
        cutoff_bound cutoff_derivative_zero_bound
        cutoff_derivative_one_bound A0_nonnegative B0_nonnegative
        B1_nonnegative coefficient_lp coefficient_support]
    by blast

  let ?T = "max TB (max TF TU)"
  show ?thesis
  proof (rule exI[of _ ?T], rule conjI)
    show "2 \<le> ?T"
      using bounded_threshold by simp
  next
    show
      "AE c in (lborel :: slp_point measure).
        c \<in> Omega \<longrightarrow>
        slp_cauchy_integrable_at SLP_Dbar_Inverse coefficient c
        \<and> (\<forall>tau. ?T \<le> tau \<longrightarrow>
          (\<exists>K::real. slp_ae_bounded_measurable lborel K
            (slp_left_neumann_series_sum X tau c cutoff coefficient))
          \<and> (AE z in lborel.
            slp_left_neumann_series_sum X tau c cutoff coefficient z =
              slp_restrict_field X
                (slp_left_neumann_base tau c cutoff coefficient
                  SLP_Dbar_Inverse) z +
              slp_restrict_field X
                (slp_left_neumann_step tau c cutoff coefficient
                  (slp_left_neumann_series_sum X tau c cutoff coefficient)) z)
          \<and> (\<forall>candidate K.
            slp_ae_bounded_measurable lborel K candidate
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
                slp_left_neumann_series_sum X tau c cutoff coefficient z)))"
      using center_integrable
    proof eventually_elim
      fix c :: slp_point
      assume c_integrable:
        "slp_cauchy_integrable_at SLP_Dbar_Inverse coefficient c"
      show
        "c \<in> Omega \<longrightarrow>
          slp_cauchy_integrable_at SLP_Dbar_Inverse coefficient c
          \<and> (\<forall>tau. ?T \<le> tau \<longrightarrow>
            (\<exists>K::real. slp_ae_bounded_measurable lborel K
              (slp_left_neumann_series_sum X tau c cutoff coefficient))
            \<and> (AE z in lborel.
              slp_left_neumann_series_sum X tau c cutoff coefficient z =
                slp_restrict_field X
                  (slp_left_neumann_base tau c cutoff coefficient
                    SLP_Dbar_Inverse) z +
                slp_restrict_field X
                  (slp_left_neumann_step tau c cutoff coefficient
                    (slp_left_neumann_series_sum X tau c cutoff coefficient)) z)
            \<and> (\<forall>candidate K.
              slp_ae_bounded_measurable lborel K candidate
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
                  slp_left_neumann_series_sum X tau c cutoff coefficient z)))"
      proof
        assume c_in: "c \<in> Omega"
        have geometry:
            "\<forall>y. y \<in> X \<longrightarrow>
              Real_Vector_Spaces.norm (y - c) \<le> R"
          using center_geometry[OF c_in] by blast
        show
          "slp_cauchy_integrable_at SLP_Dbar_Inverse coefficient c
          \<and> (\<forall>tau. ?T \<le> tau \<longrightarrow>
            (\<exists>K::real. slp_ae_bounded_measurable lborel K
              (slp_left_neumann_series_sum X tau c cutoff coefficient))
            \<and> (AE z in lborel.
              slp_left_neumann_series_sum X tau c cutoff coefficient z =
                slp_restrict_field X
                  (slp_left_neumann_base tau c cutoff coefficient
                    SLP_Dbar_Inverse) z +
                slp_restrict_field X
                  (slp_left_neumann_step tau c cutoff coefficient
                    (slp_left_neumann_series_sum X tau c cutoff coefficient)) z)
            \<and> (\<forall>candidate K.
              slp_ae_bounded_measurable lborel K candidate
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
                  slp_left_neumann_series_sum X tau c cutoff coefficient z)))"
        proof (rule conjI[OF c_integrable], intro allI impI)
          fix tau :: real
          assume tau_large: "?T \<le> tau"
          have bounded_tau: "TB \<le> tau"
            using tau_large by simp
          have fixed_tau: "TF \<le> tau"
            using tau_large by simp
          have unique_tau: "TU \<le> tau"
            using tau_large by simp
          have bounded:
              "\<exists>K::real. slp_ae_bounded_measurable lborel K
                (slp_left_neumann_series_sum X tau c cutoff coefficient)"
            using bounded_data bounded_tau geometry by blast
          have fixed:
              "AE z in lborel.
                slp_left_neumann_series_sum X tau c cutoff coefficient z =
                  slp_restrict_field X
                    (slp_left_neumann_base tau c cutoff coefficient
                      SLP_Dbar_Inverse) z +
                  slp_restrict_field X
                    (slp_left_neumann_step tau c cutoff coefficient
                      (slp_left_neumann_series_sum X tau c cutoff coefficient)) z"
            using fixed_data fixed_tau geometry by blast
          have unique:
              "\<forall>candidate K.
                slp_ae_bounded_measurable lborel K candidate
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
            fix candidate :: slp_scalar_field and K :: real
            assume candidate_data:
              "slp_ae_bounded_measurable lborel K candidate
              \<and> (AE z in lborel.
                candidate z =
                  slp_restrict_field X
                    (slp_left_neumann_base tau c cutoff coefficient
                      SLP_Dbar_Inverse) z +
                  slp_restrict_field X
                    (slp_left_neumann_step tau c cutoff coefficient candidate) z)"
            show
              "AE z in lborel.
                candidate z =
                  slp_left_neumann_series_sum X tau c cutoff coefficient z"
              by (rule unique_data[rule_format,
                    where tau = tau and c = c and candidate = candidate and K = K])
                (use unique_tau geometry candidate_data in blast)
          qed
          show
            "(\<exists>K::real. slp_ae_bounded_measurable lborel K
                (slp_left_neumann_series_sum X tau c cutoff coefficient))
            \<and> (AE z in lborel.
              slp_left_neumann_series_sum X tau c cutoff coefficient z =
                slp_restrict_field X
                  (slp_left_neumann_base tau c cutoff coefficient
                    SLP_Dbar_Inverse) z +
                slp_restrict_field X
                  (slp_left_neumann_step tau c cutoff coefficient
                    (slp_left_neumann_series_sum X tau c cutoff coefficient)) z)
            \<and> (\<forall>candidate K.
              slp_ae_bounded_measurable lborel K candidate
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
            using bounded fixed unique by blast
        qed
      qed
    qed
  qed
qed

end

end
