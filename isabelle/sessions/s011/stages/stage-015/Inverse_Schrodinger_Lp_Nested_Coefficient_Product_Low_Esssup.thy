theory Inverse_Schrodinger_Lp_Nested_Coefficient_Product_Low_Esssup
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_015.Inverse_Schrodinger_Lp_Esssup_Bounded_Multiplier"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Actual nested coefficient-product low endpoint\<close>

context aim_planar_hls_cauchy
begin

theorem slp_both_nested_coefficient_product_low_esssup_bounds:
  fixes a :: real
    and X :: "slp_point set"
    and cutoff :: slp_scalar_field
  assumes exponent_lower: "1 < a"
    and exponent_upper: "a < 2"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
    and cutoff_test: "slp_test_function_on X cutoff"
  shows
    "\<exists>C::real. 0 < C \<and>
      (\<forall>tau c coefficient multiplier M.
        aim_complex_lp_on_plane a coefficient \<and>
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
          \<le> ereal (C * M * aim_complex_lp_norm a coefficient)
        \<and>
        (\<lambda>z :: slp_point.
          ereal (Real_Vector_Spaces.norm
            (slp_restrict_field X
              (slp_dbar_psi_inverse (- tau) c
                (\<lambda>x. cutoff x *
                  slp_partial_psi_inverse (- tau) c
                    (\<lambda>y. coefficient y * multiplier y) x)) z)))
          \<in> borel_measurable (lborel :: slp_point measure)
        \<and>
        esssup (lborel :: slp_point measure)
          (\<lambda>z :: slp_point.
            ereal (Real_Vector_Spaces.norm
              (slp_restrict_field X
                (slp_dbar_psi_inverse (- tau) c
                  (\<lambda>x. cutoff x *
                    slp_partial_psi_inverse (- tau) c
                      (\<lambda>y. coefficient y * multiplier y) x)) z)))
          \<le> ereal (C * M * aim_complex_lp_norm a coefficient))"
proof -
  have exponent_positive: "0 < a"
    using exponent_lower by linarith
  obtain C :: real where C_positive: "0 < C"
    and endpoint:
      "\<forall>tau1 tau2 c1 c2 f outer inner.
        aim_complex_lp_on_plane a f \<longrightarrow>
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
          norm (slp_cauchy_transform outer
            (slp_oscillatory_modulation tau1 c1
              (\<lambda>y. cutoff y * slp_cauchy_transform inner
                (slp_oscillatory_modulation tau2 c2 f) y)) z)
            \<le> C * aim_complex_lp_norm a f)"
    using slp_two_oscillatory_cauchy_test_cutoff_bound[
      OF exponent_lower exponent_upper X_bounded cutoff_test]
    by blast
  have C_nonnegative: "0 \<le> C"
    using C_positive by linarith
  show ?thesis
  proof (rule exI[of _ C], rule conjI[OF C_positive])
    show "\<forall>tau c coefficient multiplier M.
        aim_complex_lp_on_plane a coefficient \<and>
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
          \<le> ereal (C * M * aim_complex_lp_norm a coefficient)
        \<and>
        (\<lambda>z :: slp_point.
          ereal (Real_Vector_Spaces.norm
            (slp_restrict_field X
              (slp_dbar_psi_inverse (- tau) c
                (\<lambda>x. cutoff x *
                  slp_partial_psi_inverse (- tau) c
                    (\<lambda>y. coefficient y * multiplier y) x)) z)))
          \<in> borel_measurable (lborel :: slp_point measure)
        \<and>
        esssup (lborel :: slp_point measure)
          (\<lambda>z :: slp_point.
            ereal (Real_Vector_Spaces.norm
              (slp_restrict_field X
                (slp_dbar_psi_inverse (- tau) c
                  (\<lambda>x. cutoff x *
                    slp_partial_psi_inverse (- tau) c
                      (\<lambda>y. coefficient y * multiplier y) x)) z)))
          \<le> ereal (C * M * aim_complex_lp_norm a coefficient)"
    proof (intro allI impI, elim conjE)
      fix tau :: real and c :: slp_point
        and coefficient multiplier :: slp_scalar_field and M :: real
      assume coefficient_lp: "aim_complex_lp_on_plane a coefficient"
        and multiplier_measurable:
          "multiplier \<in> borel_measurable lborel"
        and multiplier_bound:
          "AE x in lborel. norm (multiplier x) \<le> M"
        and M_nonnegative: "0 \<le> M"
      let ?source = "\<lambda>x. coefficient x * multiplier x"
      let ?left =
        "slp_partial_psi_inverse tau c
          (\<lambda>x. cutoff x * slp_dbar_psi_inverse tau c ?source x)"
      let ?right =
        "slp_dbar_psi_inverse (- tau) c
          (\<lambda>x. cutoff x *
            slp_partial_psi_inverse (- tau) c ?source x)"
      let ?E = "C * M * aim_complex_lp_norm a coefficient"
      let ?hL =
        "\<lambda>z :: slp_point.
          ereal (Real_Vector_Spaces.norm
            (slp_restrict_field X ?left z))"
      let ?hR =
        "\<lambda>z :: slp_point.
          ereal (Real_Vector_Spaces.norm
            (slp_restrict_field X ?right z))"
      note product = slp_complex_lp_AE_bounded_multiplier[
        where p=a and multiplier=multiplier and f=coefficient and C=M,
        OF exponent_positive multiplier_measurable multiplier_bound
          M_nonnegative coefficient_lp]
      have source_lp: "aim_complex_lp_on_plane a ?source"
        using product(1) by (simp only: mult.commute)
      have source_norm:
          "aim_complex_lp_norm a ?source \<le>
            M * aim_complex_lp_norm a coefficient"
        using product(2) by (simp only: mult.commute)
      have left_data:
          "?left \<in> borel_measurable lborel
          \<and>
          (\<forall>z\<in>X.
            slp_cauchy_integrable_at SLP_Partial_Inverse
              (slp_oscillatory_modulation tau c
                (\<lambda>x. cutoff x *
                  slp_dbar_psi_inverse tau c ?source x)) z
            \<and> norm (?left z) \<le>
              C * aim_complex_lp_norm a ?source)"
        using endpoint source_lp
        by (simp only: slp_partial_psi_inverse_def
            slp_dbar_psi_inverse_def; blast)
      have right_data:
          "?right \<in> borel_measurable lborel
          \<and>
          (\<forall>z\<in>X.
            slp_cauchy_integrable_at SLP_Dbar_Inverse
              (slp_oscillatory_modulation tau c
                (\<lambda>x. cutoff x *
                  slp_partial_psi_inverse (- tau) c ?source x)) z
            \<and> norm (?right z) \<le>
              C * aim_complex_lp_norm a ?source)"
        using endpoint source_lp
        by (simp only: slp_partial_psi_inverse_def
            slp_dbar_psi_inverse_def minus_minus; blast)
      have envelope_nonnegative: "0 \<le> ?E"
        unfolding aim_complex_lp_norm_def
        by (intro mult_nonneg_nonneg C_nonnegative M_nonnegative powr_ge_zero)
      have scaled_source:
          "C * aim_complex_lp_norm a ?source \<le> ?E"
        by (rule order_trans[OF mult_left_mono[OF source_norm C_nonnegative]])
          (simp only: mult.assoc)
      have left_pointwise: "norm (?left z) \<le> ?E" if "z \<in> X" for z
        by (rule order_trans[OF conjunct2[OF conjunct2[OF left_data,
              rule_format, OF that]] scaled_source])
      have right_pointwise: "norm (?right z) \<le> ?E" if "z \<in> X" for z
        by (rule order_trans[OF conjunct2[OF conjunct2[OF right_data,
              rule_format, OF that]] scaled_source])
      have left_restricted_measurable:
          "slp_restrict_field X ?left \<in> borel_measurable lborel"
        by (rule slp_restrict_field_measurable[
              OF X_measurable conjunct1[OF left_data]])
      have right_restricted_measurable:
          "slp_restrict_field X ?right \<in> borel_measurable lborel"
        by (rule slp_restrict_field_measurable[
              OF X_measurable conjunct1[OF right_data]])
      have hL_measurable:
          "?hL \<in> borel_measurable (lborel :: slp_point measure)"
        using left_restricted_measurable by measurable
      have hR_measurable:
          "?hR \<in> borel_measurable (lborel :: slp_point measure)"
        using right_restricted_measurable by measurable
      have hL_bound: "?hL z \<le> ereal ?E" for z
      proof (cases "z \<in> X")
        case True
        then show ?thesis
          using left_pointwise[OF True]
          by (simp add: slp_restrict_field_def)
      next
        case False
        then show ?thesis
          using envelope_nonnegative
          by (simp add: slp_restrict_field_def)
      qed
      have hR_bound: "?hR z \<le> ereal ?E" for z
      proof (cases "z \<in> X")
        case True
        then show ?thesis
          using right_pointwise[OF True]
          by (simp add: slp_restrict_field_def)
      next
        case False
        then show ?thesis
          using envelope_nonnegative
          by (simp add: slp_restrict_field_def)
      qed
      have hL_AE: "AE z in (lborel :: slp_point measure). ?hL z \<le> ereal ?E"
        by (rule AE_I2) (rule hL_bound)
      have hR_AE: "AE z in (lborel :: slp_point measure). ?hR z \<le> ereal ?E"
        by (rule AE_I2) (rule hR_bound)
      have hL_esssup:
          "esssup (lborel :: slp_point measure) ?hL \<le> ereal ?E"
        by (rule esssup_I[OF hL_measurable hL_AE])
      have hR_esssup:
          "esssup (lborel :: slp_point measure) ?hR \<le> ereal ?E"
        by (rule esssup_I[OF hR_measurable hR_AE])
      show "?hL \<in> borel_measurable (lborel :: slp_point measure)
          \<and> esssup (lborel :: slp_point measure) ?hL \<le> ereal ?E
          \<and> ?hR \<in> borel_measurable (lborel :: slp_point measure)
          \<and> esssup (lborel :: slp_point measure) ?hR \<le> ereal ?E"
        by (rule conjI[OF hL_measurable], rule conjI[OF hL_esssup],
            rule conjI[OF hR_measurable hR_esssup])
    qed
  qed
qed

end

end
