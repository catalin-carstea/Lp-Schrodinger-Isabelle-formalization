theory Inverse_Schrodinger_Lp_Left_Initial_Cauchy_Source_Endpoints
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_015.Inverse_Schrodinger_Lp_Nested_Coefficient_Product_High_Esssup"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_015.Inverse_Schrodinger_Lp_Nested_Coefficient_Product_Low_Esssup"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Initial Cauchy-source endpoint bounds\<close>

context aim_planar_hls_cauchy
begin

theorem slp_left_initial_cauchy_source_low_esssup_bound:
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
      (\<forall>tau c coefficient.
        aim_complex_lp_on_plane a coefficient
        \<longrightarrow>
        (\<lambda>z :: slp_point.
          ereal (Real_Vector_Spaces.norm
            (slp_restrict_field X
              (slp_partial_psi_inverse tau c
                (\<lambda>x. cutoff x * slp_dbar_inverse coefficient x)) z)))
          \<in> borel_measurable (lborel :: slp_point measure)
        \<and>
        esssup (lborel :: slp_point measure)
          (\<lambda>z :: slp_point.
            ereal (Real_Vector_Spaces.norm
              (slp_restrict_field X
                (slp_partial_psi_inverse tau c
                  (\<lambda>x. cutoff x *
                    slp_dbar_inverse coefficient x)) z)))
          \<le> ereal (C * aim_complex_lp_norm a coefficient))"
proof -
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
    show "\<forall>tau c coefficient.
        aim_complex_lp_on_plane a coefficient
        \<longrightarrow>
        (\<lambda>z :: slp_point.
          ereal (Real_Vector_Spaces.norm
            (slp_restrict_field X
              (slp_partial_psi_inverse tau c
                (\<lambda>x. cutoff x * slp_dbar_inverse coefficient x)) z)))
          \<in> borel_measurable (lborel :: slp_point measure)
        \<and>
        esssup (lborel :: slp_point measure)
          (\<lambda>z :: slp_point.
            ereal (Real_Vector_Spaces.norm
              (slp_restrict_field X
                (slp_partial_psi_inverse tau c
                  (\<lambda>x. cutoff x *
                    slp_dbar_inverse coefficient x)) z)))
          \<le> ereal (C * aim_complex_lp_norm a coefficient)"
    proof (intro allI impI)
      fix tau :: real and c :: slp_point and coefficient :: slp_scalar_field
      assume coefficient_lp: "aim_complex_lp_on_plane a coefficient"
      let ?T =
        "slp_partial_psi_inverse tau c
          (\<lambda>x. cutoff x * slp_dbar_inverse coefficient x)"
      let ?E = "C * aim_complex_lp_norm a coefficient"
      let ?h =
        "\<lambda>z :: slp_point.
          ereal (Real_Vector_Spaces.norm
            (slp_restrict_field X ?T z))"
      have zero_modulation:
          "slp_oscillatory_modulation 0 c coefficient = coefficient"
        by (rule ext)
          (simp add: slp_oscillatory_modulation_def
            slp_center_kernel_def)
      have left_data:
          "?T \<in> borel_measurable lborel
          \<and>
          (\<forall>z\<in>X.
            slp_cauchy_integrable_at SLP_Partial_Inverse
              (slp_oscillatory_modulation tau c
                (\<lambda>x. cutoff x * slp_dbar_inverse coefficient x)) z
            \<and> norm (?T z) \<le> ?E)"
      proof -
        have raw:
            "slp_cauchy_transform SLP_Partial_Inverse
              (slp_oscillatory_modulation tau c
                (\<lambda>x. cutoff x *
                  slp_cauchy_transform SLP_Dbar_Inverse
                    (slp_oscillatory_modulation 0 c coefficient) x))
              \<in> borel_measurable lborel
            \<and>
            (\<forall>z\<in>X.
              slp_cauchy_integrable_at SLP_Partial_Inverse
                (slp_oscillatory_modulation tau c
                  (\<lambda>x. cutoff x *
                    slp_cauchy_transform SLP_Dbar_Inverse
                      (slp_oscillatory_modulation 0 c coefficient) x)) z
              \<and>
              norm (slp_cauchy_transform SLP_Partial_Inverse
                (slp_oscillatory_modulation tau c
                  (\<lambda>x. cutoff x *
                    slp_cauchy_transform SLP_Dbar_Inverse
                      (slp_oscillatory_modulation 0 c coefficient) x)) z)
                \<le> C * aim_complex_lp_norm a coefficient)"
          using endpoint coefficient_lp by blast
        show ?thesis
          using raw
          unfolding slp_partial_psi_inverse_def zero_modulation .
      qed
      have E_nonnegative: "0 \<le> ?E"
        unfolding aim_complex_lp_norm_def
        by (rule mult_nonneg_nonneg[OF C_nonnegative powr_ge_zero])
      have pointwise: "norm (?T z) \<le> ?E" if "z \<in> X" for z
        using left_data that by blast
      have restricted_measurable:
          "slp_restrict_field X ?T \<in> borel_measurable lborel"
        by (rule slp_restrict_field_measurable[
              OF X_measurable conjunct1[OF left_data]])
      have h_measurable:
          "?h \<in> borel_measurable (lborel :: slp_point measure)"
        using restricted_measurable by measurable
      have h_bound: "?h z \<le> ereal ?E" for z
      proof (cases "z \<in> X")
        case True
        then show ?thesis
          using pointwise[OF True]
          by (simp add: slp_restrict_field_def)
      next
        case False
        then show ?thesis
          using E_nonnegative
          by (simp add: slp_restrict_field_def)
      qed
      have h_AE:
          "AE z in (lborel :: slp_point measure). ?h z \<le> ereal ?E"
        by (rule AE_I2) (rule h_bound)
      have h_esssup:
          "esssup (lborel :: slp_point measure) ?h \<le> ereal ?E"
        by (rule esssup_I[OF h_measurable h_AE])
      show "?h \<in> borel_measurable (lborel :: slp_point measure)
          \<and> esssup (lborel :: slp_point measure) ?h \<le> ereal ?E"
        by (rule conjI[OF h_measurable h_esssup])
    qed
  qed
qed

end

context slp_cauchy_local_w1s
begin

theorem slp_left_initial_cauchy_source_high_esssup_bound:
  fixes b A R A0 B0 B1 :: real
    and X Y :: "slp_point set"
    and cutoff :: slp_scalar_field
  assumes riesz_hls: "aim_planar_riesz_hls_claim"
    and cauchy_test_left_inverse:
      "aim_planar_cauchy_test_left_inverse_claim"
    and evans_density: "evans_compact_support_w1p_zero_density_claim"
    and exponent_above_two: "2 < b"
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
  shows
    "\<exists>C::real. 0 < C \<and>
      (\<forall>tau c coefficient.
        2 \<le> tau \<and>
        (\<forall>y. y \<in> X \<longrightarrow>
          Real_Vector_Spaces.norm (y - c) \<le> R) \<and>
        aim_complex_lp_on_plane b coefficient \<and>
        {x. coefficient x \<noteq> 0} \<subseteq> Y
        \<longrightarrow>
        (\<lambda>z :: slp_point.
          ereal (Real_Vector_Spaces.norm
            (slp_restrict_field X
              (slp_partial_psi_inverse tau c
                (\<lambda>x. cutoff x *
                  slp_dbar_inverse coefficient x)) z)))
          \<in> borel_measurable (lborel :: slp_point measure)
        \<and>
        esssup (lborel :: slp_point measure)
          (\<lambda>z :: slp_point.
            ereal (Real_Vector_Spaces.norm
              (slp_restrict_field X
                (slp_partial_psi_inverse tau c
                  (\<lambda>x. cutoff x *
                    slp_dbar_inverse coefficient x)) z)))
          \<le> ereal
            (C * inverse (sqrt tau) * ln (2 + tau) *
              aim_complex_lp_norm b coefficient))"
proof -
  obtain C :: real where C_positive: "0 < C"
    and endpoint:
      "\<forall>tau c coefficient multiplier M.
        2 \<le> tau \<and>
        (\<forall>y. y \<in> X \<longrightarrow>
          Real_Vector_Spaces.norm (y - c) \<le> R) \<and>
        aim_complex_lp_on_plane b coefficient \<and>
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
            (C * inverse (sqrt tau) * ln (2 + tau) * M *
              aim_complex_lp_norm b coefficient)"
    using slp_nested_coefficient_product_high_esssup_bound[
      OF riesz_hls cauchy_test_left_inverse evans_density
        exponent_above_two radius_nonnegative radius_lower set_radius
        X_open X_bounded Y_bounded cutoff_test cutoff_bound
        cutoff_derivative_zero_bound cutoff_derivative_one_bound
        A0_nonnegative B0_nonnegative B1_nonnegative]
    by blast
  show ?thesis
  proof (rule exI[of _ C], rule conjI[OF C_positive])
    show "\<forall>tau c coefficient.
        2 \<le> tau \<and>
        (\<forall>y. y \<in> X \<longrightarrow>
          Real_Vector_Spaces.norm (y - c) \<le> R) \<and>
        aim_complex_lp_on_plane b coefficient \<and>
        {x. coefficient x \<noteq> 0} \<subseteq> Y
        \<longrightarrow>
        (\<lambda>z :: slp_point.
          ereal (Real_Vector_Spaces.norm
            (slp_restrict_field X
              (slp_partial_psi_inverse tau c
                (\<lambda>x. cutoff x *
                  slp_dbar_inverse coefficient x)) z)))
          \<in> borel_measurable (lborel :: slp_point measure)
        \<and>
        esssup (lborel :: slp_point measure)
          (\<lambda>z :: slp_point.
            ereal (Real_Vector_Spaces.norm
              (slp_restrict_field X
                (slp_partial_psi_inverse tau c
                  (\<lambda>x. cutoff x *
                    slp_dbar_inverse coefficient x)) z)))
          \<le> ereal
            (C * inverse (sqrt tau) * ln (2 + tau) *
              aim_complex_lp_norm b coefficient)"
    proof (intro allI impI)
      fix tau :: real and c :: slp_point and coefficient :: slp_scalar_field
      assume data:
        "2 \<le> tau \<and>
          (\<forall>y. y \<in> X \<longrightarrow>
            Real_Vector_Spaces.norm (y - c) \<le> R) \<and>
          aim_complex_lp_on_plane b coefficient \<and>
          {x. coefficient x \<noteq> 0} \<subseteq> Y"
      let ?modulated = "slp_oscillatory_modulation tau c coefficient"
      let ?one = "\<lambda>_ :: slp_point. (1 :: complex)"
      have modulated_lp: "aim_complex_lp_on_plane b ?modulated"
        using data by simp
      have modulated_carrier: "{x. ?modulated x \<noteq> 0} \<subseteq> Y"
        using data by auto
      have phase_cancel:
          "slp_oscillatory_modulation (- tau) c
              (\<lambda>y. ?modulated y * ?one y) = coefficient"
      proof (rule ext)
        fix y
        show "slp_oscillatory_modulation (- tau) c
              (\<lambda>y. ?modulated y * ?one y) y = coefficient y"
          by (simp add: slp_oscillatory_modulation_def
                slp_center_kernel_def exp_add[symmetric]
                algebra_simps)
      qed
      have inner_cancel:
          "slp_dbar_psi_inverse tau c
              (\<lambda>y. ?modulated y * ?one y) =
            slp_dbar_inverse coefficient"
        unfolding slp_dbar_psi_inverse_def phase_cancel ..
      have modulated_norm:
          "aim_complex_lp_norm b ?modulated =
            aim_complex_lp_norm b coefficient"
        by simp
      have raw:
          "(\<lambda>z :: slp_point.
            ereal (Real_Vector_Spaces.norm
              (slp_restrict_field X
                (slp_partial_psi_inverse tau c
                  (\<lambda>x. cutoff x *
                    slp_dbar_psi_inverse tau c
                      (\<lambda>y. ?modulated y * ?one y) x)) z)))
            \<in> borel_measurable (lborel :: slp_point measure)
          \<and>
          esssup (lborel :: slp_point measure)
            (\<lambda>z :: slp_point.
              ereal (Real_Vector_Spaces.norm
                (slp_restrict_field X
                  (slp_partial_psi_inverse tau c
                    (\<lambda>x. cutoff x *
                      slp_dbar_psi_inverse tau c
                        (\<lambda>y. ?modulated y * ?one y) x)) z)))
            \<le> ereal
              (C * inverse (sqrt tau) * ln (2 + tau) * 1 *
                aim_complex_lp_norm b ?modulated)"
      proof (rule endpoint[rule_format, of tau c ?modulated ?one 1])
        show "2 \<le> tau \<and>
            (\<forall>y. y \<in> X \<longrightarrow>
              Real_Vector_Spaces.norm (y - c) \<le> R) \<and>
            aim_complex_lp_on_plane b ?modulated \<and>
            {x. ?modulated x \<noteq> 0} \<subseteq> Y \<and>
            ?one \<in> borel_measurable lborel \<and>
            (AE x in lborel. norm (?one x) \<le> 1) \<and>
            0 \<le> (1::real)"
          using data modulated_lp modulated_carrier by simp
      qed
      show
          "(\<lambda>z :: slp_point.
            ereal (Real_Vector_Spaces.norm
              (slp_restrict_field X
                (slp_partial_psi_inverse tau c
                  (\<lambda>x. cutoff x *
                    slp_dbar_inverse coefficient x)) z)))
            \<in> borel_measurable (lborel :: slp_point measure)
          \<and>
          esssup (lborel :: slp_point measure)
            (\<lambda>z :: slp_point.
              ereal (Real_Vector_Spaces.norm
                (slp_restrict_field X
                  (slp_partial_psi_inverse tau c
                    (\<lambda>x. cutoff x *
                      slp_dbar_inverse coefficient x)) z)))
            \<le> ereal
              (C * inverse (sqrt tau) * ln (2 + tau) *
                aim_complex_lp_norm b coefficient)"
        using raw unfolding inner_cancel modulated_norm by simp
    qed
  qed
qed

end

end
