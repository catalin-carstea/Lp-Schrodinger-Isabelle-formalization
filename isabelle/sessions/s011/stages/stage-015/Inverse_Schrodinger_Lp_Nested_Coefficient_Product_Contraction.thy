theory Inverse_Schrodinger_Lp_Nested_Coefficient_Product_Contraction
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_015.Inverse_Schrodinger_Lp_Nested_Coefficient_Product_Power_Loss_Esssup"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Concrete center-uniform contraction threshold\<close>

context slp_cauchy_local_w1s
begin

theorem slp_nested_coefficient_product_left_esssup_contraction:
  fixes p epsilon A R A0 B0 B1 :: real
    and X Y :: "slp_point set"
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
    and Y_bounded: "bounded Y"
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
    and coefficient_support: "{x. coefficient x \<noteq> 0} \<subseteq> Y"
  shows
    "\<exists>T::real. 2 \<le> T \<and>
      (\<forall>tau c multiplier M.
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
          \<le> ereal ((1 / 2) * M))"
proof -
  obtain C :: real where C_positive: "0 < C"
    and power_loss_endpoint:
      "\<forall>tau c coefficient multiplier M.
        2 \<le> tau \<and>
        (\<forall>y. y \<in> X \<longrightarrow>
          Real_Vector_Spaces.norm (y - c) \<le> R) \<and>
        aim_complex_lp_on_plane p coefficient \<and>
        {x. coefficient x \<noteq> 0} \<subseteq> Y \<and>
        multiplier \<in> borel_measurable lborel \<and>
        (AE x in lborel. norm (multiplier x) \<le> M) \<and>
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
            (C * M *
              tau powr (-(1 - 1 / p) + epsilon) *
              aim_complex_lp_norm p coefficient)"
    using slp_nested_coefficient_product_left_esssup_power_loss_bound[
        OF riesz_hls cauchy_test_left_inverse evans_density
          exponent_lower exponent_upper loss_positive radius_nonnegative
          radius_lower set_radius X_open X_bounded Y_bounded cutoff_test
          cutoff_bound cutoff_derivative_zero_bound
          cutoff_derivative_one_bound A0_nonnegative B0_nonnegative
          B1_nonnegative]
    by blast

  let ?Q = "aim_complex_lp_norm p coefficient"
  let ?alpha = "1 - 1 / p - epsilon"
  let ?CV = "C * ?Q"
  have alpha_positive: "0 < ?alpha"
    using loss_upper by linarith
  have Q_nonnegative: "0 \<le> ?Q"
    unfolding aim_complex_lp_norm_def by (rule powr_ge_zero)
  have CV_nonnegative: "0 \<le> ?CV"
    by (rule mult_nonneg_nonneg[OF less_imp_le[OF C_positive] Q_nonnegative])
  have identity_at_top:
    "filterlim (\<lambda>tau :: real. tau) at_top at_top"
    by (rule filterlim_ident)
  have powr_limit:
    "((\<lambda>tau :: real. tau powr (- ?alpha)) \<longlongrightarrow> 0) at_top"
    by (rule tendsto_neg_powr[OF _ identity_at_top])
       (use alpha_positive in simp)
  have ratio_limit:
    "((\<lambda>tau :: real. ?CV * (tau powr (- ?alpha))) \<longlongrightarrow> 0) at_top"
    using tendsto_mult_left[OF powr_limit, of ?CV]
    by simp
  have ratio_small:
    "eventually
      (\<lambda>tau :: real. dist (?CV * (tau powr (- ?alpha))) 0 < 1 / 2)
      at_top"
    by (rule tendstoD[OF ratio_limit]) simp
  have tau_positive:
    "eventually (\<lambda>tau :: real. 0 < tau) at_top"
    by simp
  have eventual_half:
    "eventually
      (\<lambda>tau :: real.
        0 < tau \<and>
        0 \<le> ?CV * (tau powr (- ?alpha)) \<and>
        ?CV * (tau powr (- ?alpha)) \<le> 1 / 2)
      at_top"
    using tau_positive ratio_small
  proof eventually_elim
    fix tau :: real
    assume tau_positive': "0 < tau"
      and ratio_small':
        "dist (?CV * (tau powr (- ?alpha))) 0 < 1 / 2"
    have ratio_nonnegative:
        "0 \<le> ?CV * (tau powr (- ?alpha))"
      by (rule mult_nonneg_nonneg[OF CV_nonnegative powr_ge_zero])
    have ratio_upper:
        "?CV * (tau powr (- ?alpha)) \<le> 1 / 2"
      using ratio_small' ratio_nonnegative
      by (simp add: dist_real_def abs_of_nonneg)
    show
      "0 < tau \<and>
        0 \<le> ?CV * (tau powr (- ?alpha)) \<and>
        ?CV * (tau powr (- ?alpha)) \<le> 1 / 2"
      using tau_positive' ratio_nonnegative ratio_upper by blast
  qed
  obtain T0 :: real where T0_property:
      "\<forall>tau. T0 \<le> tau \<longrightarrow>
        0 < tau \<and>
        0 \<le> ?CV * (tau powr (- ?alpha)) \<and>
        ?CV * (tau powr (- ?alpha)) \<le> 1 / 2"
    using eventual_half
    unfolding eventually_at_top_linorder
    by blast

  let ?T = "max 2 T0"
  show ?thesis
  proof (rule exI[of _ ?T], rule conjI)
    show "2 \<le> ?T"
      by simp
  next
    show
      "\<forall>tau c multiplier M.
        ?T \<le> tau \<and>
        (\<forall>y. y \<in> X \<longrightarrow>
          Real_Vector_Spaces.norm (y - c) \<le> R) \<and>
        multiplier \<in> borel_measurable lborel \<and>
        (AE x in lborel. norm (multiplier x) \<le> M) \<and>
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
          \<le> ereal ((1 / 2) * M)"
    proof (intro allI impI)
      fix tau :: real and c :: slp_point
        and multiplier :: slp_scalar_field and M :: real
      assume contraction_input:
        "?T \<le> tau \<and>
          (\<forall>y. y \<in> X \<longrightarrow>
            Real_Vector_Spaces.norm (y - c) \<le> R) \<and>
          multiplier \<in> borel_measurable lborel \<and>
          (AE x in lborel. norm (multiplier x) \<le> M) \<and>
          0 \<le> M"
      then have threshold_input: "T0 \<le> tau"
        and tau_lower: "2 \<le> tau"
        and center_geometry:
          "\<forall>y. y \<in> X \<longrightarrow>
            Real_Vector_Spaces.norm (y - c) \<le> R"
        and multiplier_measurable:
          "multiplier \<in> borel_measurable lborel"
        and multiplier_bound:
          "AE x in lborel. norm (multiplier x) \<le> M"
        and M_nonnegative: "0 \<le> M"
        by auto
      have ratio_half:
          "?CV * (tau powr (- ?alpha)) \<le> 1 / 2"
        using T0_property threshold_input by blast
      have endpoint_result:
        "(\<lambda>z :: slp_point.
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
              (C * M *
                tau powr (-(1 - 1 / p) + epsilon) * ?Q)"
        using power_loss_endpoint tau_lower center_geometry coefficient_lp
          coefficient_support multiplier_measurable multiplier_bound
          M_nonnegative
        by blast
      have exponent_identity:
          "-(1 - 1 / p) + epsilon = - ?alpha"
        by simp
      have real_bound:
          "C * M * tau powr (-(1 - 1 / p) + epsilon) * ?Q
            \<le> (1 / 2) * M"
      proof -
        have "(?CV * tau powr (- ?alpha)) * M \<le> (1 / 2) * M"
          by (rule mult_right_mono[OF ratio_half M_nonnegative])
        then show ?thesis
          by (simp only: exponent_identity mult.assoc mult.commute
                mult.left_commute)
      qed
      have endpoint_bound:
        "esssup (lborel :: slp_point measure)
            (\<lambda>z :: slp_point.
              ereal (Real_Vector_Spaces.norm
                (slp_restrict_field X
                  (slp_partial_psi_inverse tau c
                    (\<lambda>x. cutoff x *
                      slp_dbar_psi_inverse tau c
                        (\<lambda>y. coefficient y * multiplier y) x)) z)))
          \<le> ereal
              (C * M *
                tau powr (-(1 - 1 / p) + epsilon) * ?Q)"
        using endpoint_result by blast
      have target_bound:
        "esssup (lborel :: slp_point measure)
            (\<lambda>z :: slp_point.
              ereal (Real_Vector_Spaces.norm
                (slp_restrict_field X
                  (slp_partial_psi_inverse tau c
                  (\<lambda>x. cutoff x *
                    slp_dbar_psi_inverse tau c
                      (\<lambda>y. coefficient y * multiplier y) x)) z)))
          \<le> ereal ((1 / 2) * M)"
      proof -
        have lifted_real_bound:
            "ereal
                (C * M *
                  tau powr (-(1 - 1 / p) + epsilon) * ?Q)
              \<le> ereal ((1 / 2) * M)"
          using real_bound by simp
        show ?thesis
          by (rule order_trans[OF endpoint_bound lifted_real_bound])
      qed
      show
        "(\<lambda>z :: slp_point.
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
            \<le> ereal ((1 / 2) * M)"
        using conjunct1[OF endpoint_result] target_bound by blast
    qed
  qed
qed

end

end
