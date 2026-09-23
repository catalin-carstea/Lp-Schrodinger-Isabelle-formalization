theory Inverse_Schrodinger_Lp_Left_Neumann_Iterate_Lpstar_Geometric
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_015.Inverse_Schrodinger_Lp_Left_Initial_Correction_Lpstar"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_015.Inverse_Schrodinger_Lp_Left_Neumann_Iterate_Geometric_Contraction"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Literal left Neumann iterates in both manuscript norms\<close>

context slp_cauchy_local_w1s
begin

theorem slp_left_neumann_iterate_lpstar_geometric:
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
              (CV * tau powr (-(1 - 1 / p) + epsilon)) ^ j))"
proof -
  obtain C0 :: real where C0_positive: "0 < C0"
    and base_esssup:
      "\<forall>tau c coefficient.
        2 \<le> tau \<and>
        (\<forall>y. y \<in> X \<longrightarrow>
          Real_Vector_Spaces.norm (y - c) \<le> R) \<and>
        aim_complex_lp_on_plane p coefficient \<and>
        {x. coefficient x \<noteq> 0} \<subseteq> X
        \<longrightarrow>
        (\<lambda>z :: slp_point.
          ereal (Real_Vector_Spaces.norm
            (slp_restrict_field X
              (slp_left_neumann_base tau c cutoff coefficient
                SLP_Dbar_Inverse) z)))
          \<in> borel_measurable (lborel :: slp_point measure)
        \<and>
        esssup (lborel :: slp_point measure)
          (\<lambda>z :: slp_point.
            ereal (Real_Vector_Spaces.norm
              (slp_restrict_field X
                (slp_left_neumann_base tau c cutoff coefficient
                  SLP_Dbar_Inverse) z)))
          \<le> ereal
            (C0 * tau powr (-(1 - 1 / p) + epsilon) *
              (aim_complex_lp_norm p coefficient +
                Real_Vector_Spaces.norm
                  (slp_dbar_inverse coefficient c)))"
    using slp_left_neumann_base_esssup_power_loss_bound[
      OF riesz_hls cauchy_test_left_inverse evans_density exponent_lower
        exponent_upper loss_positive radius_nonnegative radius_lower set_radius
        X_open X_bounded X_bounded cutoff_test cutoff_bound
        cutoff_derivative_zero_bound cutoff_derivative_one_bound
        A0_nonnegative B0_nonnegative B1_nonnegative]
    by blast

  obtain CB :: real where CB_positive: "0 < CB"
    and base_lpstar:
      "\<forall>tau c coefficient.
        2 \<le> tau \<and>
        aim_complex_lp_on_plane p coefficient \<and>
        {x. coefficient x \<noteq> 0} \<subseteq> X
        \<longrightarrow>
        slp_complex_lp_on (aim_hls_target_exponent p) X
          (slp_left_neumann_base tau c cutoff coefficient
            SLP_Dbar_Inverse)
        \<and>
        slp_complex_lp_norm_on (aim_hls_target_exponent p) X
          (slp_left_neumann_base tau c cutoff coefficient
            SLP_Dbar_Inverse)
          \<le> CB * inverse (sqrt tau) *
            (aim_complex_lp_norm p coefficient +
              Real_Vector_Spaces.norm
                (slp_dbar_inverse coefficient c))"
    using slp_left_neumann_base_lpstar_inverse_sqrt_bound[
      OF riesz_hls cauchy_test_left_inverse evans_density exponent_lower
        exponent_upper X_open X_bounded X_bounded cutoff_test cutoff_bound
        cutoff_derivative_zero_bound cutoff_derivative_one_bound
        A0_nonnegative B0_nonnegative B1_nonnegative]
    by blast

  obtain CS :: real where CS_positive: "0 < CS"
    and step_esssup:
      "\<forall>tau c coefficient multiplier M.
        2 \<le> tau \<and>
        (\<forall>y. y \<in> X \<longrightarrow>
          Real_Vector_Spaces.norm (y - c) \<le> R) \<and>
        aim_complex_lp_on_plane p coefficient \<and>
        {x. coefficient x \<noteq> 0} \<subseteq> X \<and>
        multiplier \<in> borel_measurable lborel \<and>
        (AE x in lborel. Real_Vector_Spaces.norm (multiplier x) \<le> M) \<and>
        0 \<le> M
        \<longrightarrow>
        (\<lambda>z :: slp_point.
          ereal (Real_Vector_Spaces.norm
            (slp_restrict_field X
              (slp_partial_psi_inverse tau c
                (\<lambda>x. cutoff x *
                  slp_dbar_psi_inverse tau c
                    (\<lambda>y. coefficient y * multiplier y) x)) z)))
          \<in> borel_measurable (lborel :: slp_point measure)
        \<and>
        esssup (lborel :: slp_point measure)
          (\<lambda>z :: slp_point.
            ereal (Real_Vector_Spaces.norm
              (slp_restrict_field X
                (slp_partial_psi_inverse tau c
                  (\<lambda>x. cutoff x *
                    slp_dbar_psi_inverse tau c
                      (\<lambda>y. coefficient y * multiplier y) x)) z)))
          \<le> ereal
            (CS * M * tau powr (-(1 - 1 / p) + epsilon) *
              aim_complex_lp_norm p coefficient)"
    using slp_nested_coefficient_product_left_esssup_power_loss_bound[
      OF riesz_hls cauchy_test_left_inverse evans_density exponent_lower
        exponent_upper loss_positive radius_nonnegative radius_lower set_radius
        X_open X_bounded X_bounded cutoff_test cutoff_bound
        cutoff_derivative_zero_bound cutoff_derivative_one_bound
        A0_nonnegative B0_nonnegative B1_nonnegative]
    by blast

  obtain CP :: real where CP_positive: "0 < CP"
    and step_lpstar:
      "\<forall>tau c coefficient multiplier M.
        2 \<le> tau \<and>
        aim_complex_lp_on_plane p coefficient \<and>
        {x. coefficient x \<noteq> 0} \<subseteq> X \<and>
        multiplier \<in> borel_measurable lborel \<and>
        (AE x in lborel. Real_Vector_Spaces.norm (multiplier x) \<le> M) \<and>
        0 \<le> M
        \<longrightarrow>
        slp_complex_lp_on (aim_hls_target_exponent p) X
          (slp_partial_psi_inverse tau c
            (\<lambda>x. cutoff x *
              slp_dbar_psi_inverse tau c
                (\<lambda>y. coefficient y * multiplier y) x))
        \<and>
        slp_complex_lp_norm_on (aim_hls_target_exponent p) X
          (slp_partial_psi_inverse tau c
            (\<lambda>x. cutoff x *
              slp_dbar_psi_inverse tau c
                (\<lambda>y. coefficient y * multiplier y) x))
          \<le> CP * inverse (sqrt tau) * M *
            aim_complex_lp_norm p coefficient"
    using slp_both_nested_coefficient_product_lpstar_inverse_sqrt_bounds[
      OF riesz_hls cauchy_test_left_inverse evans_density exponent_lower
        exponent_upper X_open X_bounded X_bounded cutoff_test cutoff_bound
        cutoff_derivative_zero_bound cutoff_derivative_one_bound
        A0_nonnegative B0_nonnegative B1_nonnegative]
    by blast

  let ?Q = "aim_complex_lp_norm p coefficient"
  let ?CV = "(CS + 1) * (?Q + 1)"
  let ?C = "max C0 (max CB (CP * C0))"
  let ?alpha = "1 - 1 / p - epsilon"

  have Q_nonnegative: "0 \<le> ?Q"
    unfolding aim_complex_lp_norm_def by (rule powr_ge_zero)
  have CV_positive: "0 < ?CV"
    by (rule mult_pos_pos) (use CS_positive Q_nonnegative in linarith)+
  have CSQ_nonnegative: "0 \<le> CS * ?Q"
    by (rule mult_nonneg_nonneg[OF less_imp_le[OF CS_positive]
          Q_nonnegative])
  have CV_expansion:
      "?CV = CS * ?Q + CS + ?Q + 1"
    by (simp add: algebra_simps)
  have CSQ_le_CV: "CS * ?Q \<le> ?CV"
    using CS_positive Q_nonnegative
    unfolding CV_expansion by linarith
  have Q_le_CV: "?Q \<le> ?CV"
    using CS_positive CSQ_nonnegative
    unfolding CV_expansion by linarith
  have C_positive: "0 < ?C"
    using C0_positive by simp
  have C0_le_C: "C0 \<le> ?C" by simp
  have CB_le_C: "CB \<le> ?C" by simp
  have CPC0_le_C: "CP * C0 \<le> ?C" by simp
  have alpha_positive: "0 < ?alpha"
    using loss_upper by linarith
  have exponent_identity:
      "-(1 - 1 / p) + epsilon = - ?alpha"
    by simp

  have identity_at_top:
      "filterlim (\<lambda>tau :: real. tau) at_top at_top"
    by (rule filterlim_ident)
  have powr_limit:
      "((\<lambda>tau :: real. tau powr (- ?alpha)) \<longlongrightarrow> 0) at_top"
    by (rule tendsto_neg_powr[OF _ identity_at_top])
       (use alpha_positive in simp)
  have rho_limit:
      "((\<lambda>tau :: real. ?CV * tau powr (- ?alpha)) \<longlongrightarrow> 0)
        at_top"
    using tendsto_mult_left[OF powr_limit, of ?CV]
    by simp
  have rho_small:
      "eventually
        (\<lambda>tau :: real. dist (?CV * tau powr (- ?alpha)) 0 < 1 / 2)
        at_top"
    by (rule tendstoD[OF rho_limit]) simp
  have tau_positive_eventually:
      "eventually (\<lambda>tau :: real. 0 < tau) at_top"
    by simp
  have eventual_half:
      "eventually
        (\<lambda>tau :: real.
          0 < tau \<and>
          0 \<le> ?CV * tau powr (- ?alpha) \<and>
          ?CV * tau powr (- ?alpha) \<le> 1 / 2)
        at_top"
    using tau_positive_eventually rho_small
  proof eventually_elim
    fix tau :: real
    assume tau_positive: "0 < tau"
      and rho_small': "dist (?CV * tau powr (- ?alpha)) 0 < 1 / 2"
    have rho_nonnegative: "0 \<le> ?CV * tau powr (- ?alpha)"
      by (rule mult_nonneg_nonneg[OF less_imp_le[OF CV_positive] powr_ge_zero])
    have rho_upper: "?CV * tau powr (- ?alpha) \<le> 1 / 2"
      using rho_small' rho_nonnegative
      by (simp add: dist_real_def abs_of_nonneg)
    show
      "0 < tau \<and>
        0 \<le> ?CV * tau powr (- ?alpha) \<and>
        ?CV * tau powr (- ?alpha) \<le> 1 / 2"
      using tau_positive rho_nonnegative rho_upper by blast
  qed
  obtain T0 :: real where T0_property:
      "\<forall>tau. T0 \<le> tau \<longrightarrow>
        0 < tau \<and>
        0 \<le> ?CV * tau powr (- ?alpha) \<and>
        ?CV * tau powr (- ?alpha) \<le> 1 / 2"
    using eventual_half
    unfolding eventually_at_top_linorder
    by blast
  let ?T = "max 2 T0"

  show ?thesis
  proof (rule exI[of _ ?C], rule exI[of _ ?CV], rule exI[of _ ?T])
    show
      "0 < ?C \<and> 0 < ?CV \<and> 2 \<le> ?T \<and>
        (\<forall>tau c.
          ?T \<le> tau \<and>
          (\<forall>y. y \<in> X \<longrightarrow>
            Real_Vector_Spaces.norm (y - c) \<le> R)
          \<longrightarrow>
          ?CV * tau powr (-(1 - 1 / p) + epsilon) \<le> 1 / 2 \<and>
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
                (?C * tau powr (-(1 - 1 / p) + epsilon) *
                  (?Q + Real_Vector_Spaces.norm
                    (slp_dbar_inverse coefficient c)) *
                  (?CV * tau powr (-(1 - 1 / p) + epsilon)) ^ j)
            \<and>
            (AE z in lborel.
              Real_Vector_Spaces.norm
                (slp_restrict_field X
                  (slp_neumann_iterate
                    (slp_left_neumann_step tau c cutoff coefficient)
                    (slp_left_neumann_base tau c cutoff coefficient
                      SLP_Dbar_Inverse) j) z)
                \<le> ?C * tau powr (-(1 - 1 / p) + epsilon) *
                  (?Q + Real_Vector_Spaces.norm
                    (slp_dbar_inverse coefficient c)) *
                  (?CV * tau powr (-(1 - 1 / p) + epsilon)) ^ j)
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
              \<le> ?C * inverse (sqrt tau) *
                (?Q + Real_Vector_Spaces.norm
                  (slp_dbar_inverse coefficient c)) *
                (?CV * tau powr (-(1 - 1 / p) + epsilon)) ^ j))"
    proof (rule conjI[OF C_positive], rule conjI[OF CV_positive], rule conjI)
      show "2 \<le> ?T" by simp
    next
      show
        "\<forall>tau c.
          ?T \<le> tau \<and>
          (\<forall>y. y \<in> X \<longrightarrow>
            Real_Vector_Spaces.norm (y - c) \<le> R)
          \<longrightarrow>
          ?CV * tau powr (-(1 - 1 / p) + epsilon) \<le> 1 / 2 \<and>
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
                (?C * tau powr (-(1 - 1 / p) + epsilon) *
                  (?Q + Real_Vector_Spaces.norm
                    (slp_dbar_inverse coefficient c)) *
                  (?CV * tau powr (-(1 - 1 / p) + epsilon)) ^ j)
            \<and>
            (AE z in lborel.
              Real_Vector_Spaces.norm
                (slp_restrict_field X
                  (slp_neumann_iterate
                    (slp_left_neumann_step tau c cutoff coefficient)
                    (slp_left_neumann_base tau c cutoff coefficient
                      SLP_Dbar_Inverse) j) z)
                \<le> ?C * tau powr (-(1 - 1 / p) + epsilon) *
                  (?Q + Real_Vector_Spaces.norm
                    (slp_dbar_inverse coefficient c)) *
                  (?CV * tau powr (-(1 - 1 / p) + epsilon)) ^ j)
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
              \<le> ?C * inverse (sqrt tau) *
                (?Q + Real_Vector_Spaces.norm
                  (slp_dbar_inverse coefficient c)) *
                (?CV * tau powr (-(1 - 1 / p) + epsilon)) ^ j)"
      proof (intro allI impI)
      fix tau :: real and c :: slp_point
      assume threshold_geometry:
        "?T \<le> tau \<and>
          (\<forall>y. y \<in> X \<longrightarrow>
            Real_Vector_Spaces.norm (y - c) \<le> R)"
      then have T0_lower: "T0 \<le> tau"
        and tau_lower: "2 \<le> tau"
        and center_geometry:
          "\<forall>y. y \<in> X \<longrightarrow>
            Real_Vector_Spaces.norm (y - c) \<le> R"
        by auto
      let ?rate = "tau powr (-(1 - 1 / p) + epsilon)"
      let ?rho = "?CV * ?rate"
      let ?B =
        "?Q + Real_Vector_Spaces.norm (slp_dbar_inverse coefficient c)"
      let ?M0 = "C0 * ?rate * ?B"
      let ?step = "slp_left_neumann_step tau c cutoff coefficient"
      let ?base =
        "slp_left_neumann_base tau c cutoff coefficient SLP_Dbar_Inverse"
      have rho_nonnegative: "0 \<le> ?rho"
        using T0_property[rule_format, OF T0_lower]
        unfolding exponent_identity by blast
      have rho_power_nonnegative: "0 \<le> ?rho ^ j" for j
        by (rule zero_le_power[OF rho_nonnegative])
      have rho_upper: "?rho \<le> 1 / 2"
        using T0_property[rule_format, OF T0_lower]
        unfolding exponent_identity by blast
      have rate_nonnegative: "0 \<le> ?rate"
        by (rule powr_ge_zero)
      have B_nonnegative: "0 \<le> ?B"
        using Q_nonnegative by simp
      have M0_nonnegative: "0 \<le> ?M0"
        by (rule mult_nonneg_nonneg[OF mult_nonneg_nonneg[
              OF less_imp_le[OF C0_positive] rate_nonnegative] B_nonnegative])
      have X_measurable: "X \<in> sets lborel"
        using X_open by simp

      have source_restrict_eq:
          "(\<lambda>y. coefficient y * f y) =
            (\<lambda>y. coefficient y * slp_restrict_field X f y)"
        for f :: slp_scalar_field
      proof (rule ext)
        fix y :: slp_point
        show "coefficient y * f y =
            coefficient y * slp_restrict_field X f y"
        proof (cases "y \<in> X")
          case True
          then show ?thesis by (simp add: slp_restrict_field_def)
        next
          case False
          then have "coefficient y = 0"
            using coefficient_support by auto
          then show ?thesis by simp
        qed
      qed
      have step_restrict_eq:
          "?step f = ?step (slp_restrict_field X f)"
        for f :: slp_scalar_field
        unfolding slp_left_neumann_step_def
        apply (subst source_restrict_eq)
        apply (rule refl)
        done

      have all_iterates:
          "\<forall>j.
            slp_restrict_field X (slp_neumann_iterate ?step ?base j)
              \<in> borel_measurable lborel
            \<and>
            (\<lambda>z :: slp_point.
              ereal (Real_Vector_Spaces.norm
                (slp_restrict_field X
                  (slp_neumann_iterate ?step ?base j) z)))
              \<in> borel_measurable (lborel :: slp_point measure)
            \<and>
            esssup (lborel :: slp_point measure)
              (\<lambda>z :: slp_point.
                ereal (Real_Vector_Spaces.norm
                  (slp_restrict_field X
                    (slp_neumann_iterate ?step ?base j) z)))
              \<le> ereal (?M0 * ?rho ^ j)
            \<and>
            (AE z in lborel.
              Real_Vector_Spaces.norm
                (slp_restrict_field X
                  (slp_neumann_iterate ?step ?base j) z)
                \<le> ?M0 * ?rho ^ j)
            \<and>
            slp_complex_lp_on (aim_hls_target_exponent p) X
              (slp_neumann_iterate ?step ?base j)
            \<and>
            slp_complex_lp_norm_on (aim_hls_target_exponent p) X
              (slp_neumann_iterate ?step ?base j)
              \<le> ?C * inverse (sqrt tau) * ?B * ?rho ^ j"
      proof
        fix j :: nat
        show
          "slp_restrict_field X (slp_neumann_iterate ?step ?base j)
              \<in> borel_measurable lborel
            \<and>
            (\<lambda>z :: slp_point.
              ereal (Real_Vector_Spaces.norm
                (slp_restrict_field X
                  (slp_neumann_iterate ?step ?base j) z)))
              \<in> borel_measurable (lborel :: slp_point measure)
            \<and>
            esssup (lborel :: slp_point measure)
              (\<lambda>z :: slp_point.
                ereal (Real_Vector_Spaces.norm
                  (slp_restrict_field X
                    (slp_neumann_iterate ?step ?base j) z)))
              \<le> ereal (?M0 * ?rho ^ j)
            \<and>
            (AE z in lborel.
              Real_Vector_Spaces.norm
                (slp_restrict_field X
                  (slp_neumann_iterate ?step ?base j) z)
                \<le> ?M0 * ?rho ^ j)
            \<and>
            slp_complex_lp_on (aim_hls_target_exponent p) X
              (slp_neumann_iterate ?step ?base j)
            \<and>
            slp_complex_lp_norm_on (aim_hls_target_exponent p) X
              (slp_neumann_iterate ?step ?base j)
              \<le> ?C * inverse (sqrt tau) * ?B * ?rho ^ j"
        proof (induction j)
          case 0
          have base_endpoint:
              "(\<lambda>z :: slp_point.
                ereal (Real_Vector_Spaces.norm
                  (slp_restrict_field X ?base z)))
                \<in> borel_measurable (lborel :: slp_point measure)
              \<and>
              esssup (lborel :: slp_point measure)
                (\<lambda>z :: slp_point.
                  ereal (Real_Vector_Spaces.norm
                    (slp_restrict_field X ?base z)))
                \<le> ereal ?M0"
            using base_esssup tau_lower center_geometry coefficient_lp
              coefficient_support by blast
          have base_lpstar_endpoint:
              "slp_complex_lp_on (aim_hls_target_exponent p) X ?base
              \<and>
              slp_complex_lp_norm_on (aim_hls_target_exponent p) X ?base
                \<le> CB * inverse (sqrt tau) * ?B"
            using base_lpstar tau_lower coefficient_lp coefficient_support
            by blast
          have base_measurable:
              "slp_restrict_field X ?base \<in> borel_measurable lborel"
            using conjunct1[OF base_lpstar_endpoint]
            unfolding slp_complex_lp_on_def aim_complex_lp_on_plane_def
            by blast
          have base_norm_measurable:
              "(\<lambda>z :: slp_point.
                ereal (Real_Vector_Spaces.norm
                  (slp_restrict_field X ?base z)))
                \<in> borel_measurable (lborel :: slp_point measure)"
            using base_endpoint by blast
          have base_esssup_bound:
              "esssup (lborel :: slp_point measure)
                (\<lambda>z :: slp_point.
                  ereal (Real_Vector_Spaces.norm
                    (slp_restrict_field X ?base z)))
                \<le> ereal ?M0"
            using base_endpoint by blast
          have base_AE:
              "AE z in lborel.
                Real_Vector_Spaces.norm (slp_restrict_field X ?base z)
                  \<le> ?M0"
            by (rule slp_ereal_norm_esssup_bound_imp_AE[
                  OF base_norm_measurable base_esssup_bound])
          have inverse_sqrt_nonnegative: "0 \<le> inverse (sqrt tau)"
            using tau_lower by simp
          have base_common_nonnegative:
              "0 \<le> inverse (sqrt tau) * ?B"
            by (rule mult_nonneg_nonneg[OF inverse_sqrt_nonnegative
                  B_nonnegative])
          have base_lpstar_bound:
              "slp_complex_lp_norm_on (aim_hls_target_exponent p) X ?base
                \<le> ?C * inverse (sqrt tau) * ?B"
          proof -
            have "CB * (inverse (sqrt tau) * ?B)
                \<le> ?C * (inverse (sqrt tau) * ?B)"
              by (rule mult_right_mono[OF CB_le_C base_common_nonnegative])
            then show ?thesis
              using conjunct2[OF base_lpstar_endpoint]
              by (simp only: mult.assoc)
          qed
          show ?case
            using base_measurable base_norm_measurable base_esssup_bound
              base_AE conjunct1[OF base_lpstar_endpoint] base_lpstar_bound
            by (simp only: slp_neumann_iterate_zero power_0 mult_1_right)
        next
          case (Suc j)
          let ?u =
            "slp_restrict_field X (slp_neumann_iterate ?step ?base j)"
          let ?Mj = "?M0 * ?rho ^ j"
          let ?v =
            "slp_restrict_field X
              (slp_neumann_iterate ?step ?base (Suc j))"
          have u_measurable: "?u \<in> borel_measurable lborel"
            using Suc.IH by blast
          have u_AE:
              "AE z in lborel. Real_Vector_Spaces.norm (?u z) \<le> ?Mj"
            using Suc.IH by blast
          have Mj_nonnegative: "0 \<le> ?Mj"
            by (rule mult_nonneg_nonneg[OF M0_nonnegative
                  rho_power_nonnegative])
          have successor_field:
              "slp_neumann_iterate ?step ?base (Suc j) = ?step ?u"
            unfolding slp_neumann_iterate_Suc
            apply (subst step_restrict_eq)
            apply (rule refl)
            done
          have step_esssup_result:
              "(\<lambda>z :: slp_point.
                ereal (Real_Vector_Spaces.norm
                  (slp_restrict_field X (?step ?u) z)))
                \<in> borel_measurable (lborel :: slp_point measure)
              \<and>
              esssup (lborel :: slp_point measure)
                (\<lambda>z :: slp_point.
                  ereal (Real_Vector_Spaces.norm
                    (slp_restrict_field X (?step ?u) z)))
                \<le> ereal (CS * ?Mj * ?rate * ?Q)"
            using step_esssup tau_lower center_geometry coefficient_lp
              coefficient_support u_measurable u_AE Mj_nonnegative
            unfolding slp_left_neumann_step_def
            by blast
          have step_lpstar_result:
              "slp_complex_lp_on (aim_hls_target_exponent p) X (?step ?u)
              \<and>
              slp_complex_lp_norm_on (aim_hls_target_exponent p) X (?step ?u)
                \<le> CP * inverse (sqrt tau) * ?Mj * ?Q"
            using step_lpstar tau_lower coefficient_lp coefficient_support
              u_measurable u_AE Mj_nonnegative
            unfolding slp_left_neumann_step_def
            by blast
          have step_measurable:
              "slp_restrict_field X (?step ?u) \<in> borel_measurable lborel"
            using conjunct1[OF step_lpstar_result]
            unfolding slp_complex_lp_on_def aim_complex_lp_on_plane_def
            by blast
          have step_norm_measurable:
              "(\<lambda>z :: slp_point.
                ereal (Real_Vector_Spaces.norm
                  (slp_restrict_field X (?step ?u) z)))
                \<in> borel_measurable (lborel :: slp_point measure)"
            using step_esssup_result by blast
          have rate_Mj_nonnegative: "0 \<le> ?Mj * ?rate"
            by (rule mult_nonneg_nonneg[OF Mj_nonnegative rate_nonnegative])
          have step_real_bound:
              "CS * ?Mj * ?rate * ?Q \<le> ?M0 * ?rho ^ Suc j"
          proof -
            have "(?Mj * ?rate) * (CS * ?Q)
                \<le> (?Mj * ?rate) * ?CV"
              by (rule mult_left_mono[OF CSQ_le_CV rate_Mj_nonnegative])
            then show ?thesis
              by (simp only: power_Suc mult.assoc mult.commute
                  mult.left_commute)
          qed
          have step_esssup_bound:
              "esssup (lborel :: slp_point measure)
                (\<lambda>z :: slp_point.
                  ereal (Real_Vector_Spaces.norm
                    (slp_restrict_field X (?step ?u) z)))
                \<le> ereal (?M0 * ?rho ^ Suc j)"
          proof -
            have raw:
                "esssup (lborel :: slp_point measure)
                  (\<lambda>z :: slp_point.
                    ereal (Real_Vector_Spaces.norm
                      (slp_restrict_field X (?step ?u) z)))
                  \<le> ereal (CS * ?Mj * ?rate * ?Q)"
              using step_esssup_result by blast
            have embedded:
                "ereal (CS * ?Mj * ?rate * ?Q)
                  \<le> ereal (?M0 * ?rho ^ Suc j)"
              using step_real_bound by simp
            show ?thesis by (rule order_trans[OF raw embedded])
          qed
          have step_AE:
              "AE z in lborel.
                Real_Vector_Spaces.norm
                  (slp_restrict_field X (?step ?u) z)
                  \<le> ?M0 * ?rho ^ Suc j"
            by (rule slp_ereal_norm_esssup_bound_imp_AE[
                  OF step_norm_measurable step_esssup_bound])
          have inverse_sqrt_nonnegative: "0 \<le> inverse (sqrt tau)"
            using tau_lower by simp
          have secondary_common_nonnegative:
              "0 \<le> CP * C0 * inverse (sqrt tau) * ?B * ?rho ^ j * ?rate"
            by (intro mult_nonneg_nonneg less_imp_le[OF CP_positive]
                  less_imp_le[OF C0_positive] inverse_sqrt_nonnegative
                  B_nonnegative rho_power_nonnegative rate_nonnegative)
          have raw_secondary_bound:
              "CP * inverse (sqrt tau) * ?Mj * ?Q
                \<le> CP * C0 * inverse (sqrt tau) * ?B * ?rho ^ Suc j"
          proof -
            have
              "(CP * C0 * inverse (sqrt tau) * ?B * ?rho ^ j * ?rate) * ?Q
                \<le>
               (CP * C0 * inverse (sqrt tau) * ?B * ?rho ^ j * ?rate) * ?CV"
              by (rule mult_left_mono[OF Q_le_CV
                    secondary_common_nonnegative])
            then show ?thesis
              by (simp only: power_Suc mult.assoc mult.commute
                  mult.left_commute)
          qed
          have final_secondary_common_nonnegative:
              "0 \<le> inverse (sqrt tau) * ?B * ?rho ^ Suc j"
            by (intro mult_nonneg_nonneg inverse_sqrt_nonnegative B_nonnegative
                  rho_power_nonnegative)
          have enlarged_secondary_bound:
              "CP * C0 * inverse (sqrt tau) * ?B * ?rho ^ Suc j
                \<le> ?C * inverse (sqrt tau) * ?B * ?rho ^ Suc j"
          proof -
            have
              "(CP * C0) * (inverse (sqrt tau) * ?B * ?rho ^ Suc j)
                \<le> ?C * (inverse (sqrt tau) * ?B * ?rho ^ Suc j)"
              by (rule mult_right_mono[OF CPC0_le_C
                    final_secondary_common_nonnegative])
            then show ?thesis
              by (simp only: mult.assoc)
          qed
          have step_lpstar_bound:
              "slp_complex_lp_norm_on (aim_hls_target_exponent p) X (?step ?u)
                \<le> ?C * inverse (sqrt tau) * ?B * ?rho ^ Suc j"
            by (rule order_trans[OF conjunct2[OF step_lpstar_result]
                  order_trans[OF raw_secondary_bound enlarged_secondary_bound]])
          show ?case
            using step_measurable step_norm_measurable step_esssup_bound step_AE
              conjunct1[OF step_lpstar_result] step_lpstar_bound
            unfolding successor_field
            by blast
        qed
      qed

      have enlarged_all_iterates:
          "\<forall>j.
            slp_restrict_field X (slp_neumann_iterate ?step ?base j)
              \<in> borel_measurable lborel
            \<and>
            (\<lambda>z :: slp_point.
              ereal (Real_Vector_Spaces.norm
                (slp_restrict_field X
                  (slp_neumann_iterate ?step ?base j) z)))
              \<in> borel_measurable (lborel :: slp_point measure)
            \<and>
            esssup (lborel :: slp_point measure)
              (\<lambda>z :: slp_point.
                ereal (Real_Vector_Spaces.norm
                  (slp_restrict_field X
                    (slp_neumann_iterate ?step ?base j) z)))
              \<le> ereal (?C * ?rate * ?B * ?rho ^ j)
            \<and>
            (AE z in lborel.
              Real_Vector_Spaces.norm
                (slp_restrict_field X
                  (slp_neumann_iterate ?step ?base j) z)
                \<le> ?C * ?rate * ?B * ?rho ^ j)
            \<and>
            slp_complex_lp_on (aim_hls_target_exponent p) X
              (slp_neumann_iterate ?step ?base j)
            \<and>
            slp_complex_lp_norm_on (aim_hls_target_exponent p) X
              (slp_neumann_iterate ?step ?base j)
              \<le> ?C * inverse (sqrt tau) * ?B * ?rho ^ j"
      proof
        fix j :: nat
        note raw = all_iterates[rule_format, of j]
        have raw_scalar_nonnegative:
            "0 \<le> ?rate * ?B * ?rho ^ j"
          by (intro mult_nonneg_nonneg rate_nonnegative B_nonnegative
                rho_power_nonnegative)
        have initial_enlargement:
            "?M0 * ?rho ^ j \<le> ?C * ?rate * ?B * ?rho ^ j"
        proof -
          have "C0 * (?rate * ?B * ?rho ^ j)
              \<le> ?C * (?rate * ?B * ?rho ^ j)"
            by (rule mult_right_mono[OF C0_le_C raw_scalar_nonnegative])
          then show ?thesis by (simp only: mult.assoc)
        qed
        have esssup_enlarged:
            "esssup (lborel :: slp_point measure)
              (\<lambda>z :: slp_point.
                ereal (Real_Vector_Spaces.norm
                  (slp_restrict_field X
                    (slp_neumann_iterate ?step ?base j) z)))
              \<le> ereal (?C * ?rate * ?B * ?rho ^ j)"
        proof -
          have raw_esssup:
              "esssup (lborel :: slp_point measure)
                (\<lambda>z :: slp_point.
                  ereal (Real_Vector_Spaces.norm
                    (slp_restrict_field X
                      (slp_neumann_iterate ?step ?base j) z)))
                \<le> ereal (?M0 * ?rho ^ j)"
            using raw by blast
          have embedded:
              "ereal (?M0 * ?rho ^ j)
                \<le> ereal (?C * ?rate * ?B * ?rho ^ j)"
            using initial_enlargement by simp
          show ?thesis by (rule order_trans[OF raw_esssup embedded])
        qed
        have raw_AE:
            "AE z in lborel.
              Real_Vector_Spaces.norm
                (slp_restrict_field X
                  (slp_neumann_iterate ?step ?base j) z)
                \<le> ?M0 * ?rho ^ j"
          using raw by blast
        have AE_enlarged:
            "AE z in lborel.
              Real_Vector_Spaces.norm
                (slp_restrict_field X
                  (slp_neumann_iterate ?step ?base j) z)
                \<le> ?C * ?rate * ?B * ?rho ^ j"
          using raw_AE
        proof eventually_elim
          fix z :: slp_point
          assume at_z:
              "Real_Vector_Spaces.norm
                (slp_restrict_field X
                  (slp_neumann_iterate ?step ?base j) z)
                \<le> ?M0 * ?rho ^ j"
          show
              "Real_Vector_Spaces.norm
                (slp_restrict_field X
                  (slp_neumann_iterate ?step ?base j) z)
                \<le> ?C * ?rate * ?B * ?rho ^ j"
            by (rule order_trans[OF at_z initial_enlargement])
        qed
        show
          "slp_restrict_field X (slp_neumann_iterate ?step ?base j)
              \<in> borel_measurable lborel
            \<and>
            (\<lambda>z :: slp_point.
              ereal (Real_Vector_Spaces.norm
                (slp_restrict_field X
                  (slp_neumann_iterate ?step ?base j) z)))
              \<in> borel_measurable (lborel :: slp_point measure)
            \<and>
            esssup (lborel :: slp_point measure)
              (\<lambda>z :: slp_point.
                ereal (Real_Vector_Spaces.norm
                  (slp_restrict_field X
                    (slp_neumann_iterate ?step ?base j) z)))
              \<le> ereal (?C * ?rate * ?B * ?rho ^ j)
            \<and>
            (AE z in lborel.
              Real_Vector_Spaces.norm
                (slp_restrict_field X
                  (slp_neumann_iterate ?step ?base j) z)
                \<le> ?C * ?rate * ?B * ?rho ^ j)
            \<and>
            slp_complex_lp_on (aim_hls_target_exponent p) X
              (slp_neumann_iterate ?step ?base j)
            \<and>
            slp_complex_lp_norm_on (aim_hls_target_exponent p) X
              (slp_neumann_iterate ?step ?base j)
              \<le> ?C * inverse (sqrt tau) * ?B * ?rho ^ j"
          using raw esssup_enlarged AE_enlarged by blast
      qed

      show
        "?CV * tau powr (-(1 - 1 / p) + epsilon) \<le> 1 / 2 \<and>
          (\<forall>j.
            slp_restrict_field X
                (slp_neumann_iterate ?step ?base j)
              \<in> borel_measurable lborel
            \<and>
            (\<lambda>z :: slp_point.
              ereal (Real_Vector_Spaces.norm
                (slp_restrict_field X
                  (slp_neumann_iterate ?step ?base j) z)))
              \<in> borel_measurable (lborel :: slp_point measure)
            \<and>
            esssup (lborel :: slp_point measure)
              (\<lambda>z :: slp_point.
                ereal (Real_Vector_Spaces.norm
                  (slp_restrict_field X
                    (slp_neumann_iterate ?step ?base j) z)))
              \<le> ereal (?C * ?rate * ?B * ?rho ^ j)
            \<and>
            (AE z in lborel.
              Real_Vector_Spaces.norm
                (slp_restrict_field X
                  (slp_neumann_iterate ?step ?base j) z)
                \<le> ?C * ?rate * ?B * ?rho ^ j)
            \<and>
            slp_complex_lp_on (aim_hls_target_exponent p) X
              (slp_neumann_iterate ?step ?base j)
            \<and>
            slp_complex_lp_norm_on (aim_hls_target_exponent p) X
              (slp_neumann_iterate ?step ?base j)
              \<le> ?C * inverse (sqrt tau) * ?B * ?rho ^ j)"
        apply (rule conjI)
         apply (rule rho_upper)
        by (rule enlarged_all_iterates)
    qed
  qed
qed
qed

end

end
