theory Inverse_Schrodinger_Lp_Left_Initial_Correction_Power_Loss
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_015.Inverse_Schrodinger_Lp_Left_Initial_Cauchy_Source_Power_Loss"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_015.Inverse_Schrodinger_Lp_Left_Initial_Center_Value_Power_Loss"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_014.Inverse_Schrodinger_Lp_Exact_Neumann_Iterate_Bridge"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Literal left initial-correction power-loss bound\<close>

context slp_cauchy_local_w1s
begin

theorem slp_left_neumann_base_esssup_power_loss_bound:
  fixes p epsilon A R A0 B0 B1 :: real
    and X Y :: "slp_point set"
    and cutoff :: slp_scalar_field
  assumes riesz_hls: "aim_planar_riesz_hls_claim"
    and cauchy_test_left_inverse:
      "aim_planar_cauchy_test_left_inverse_claim"
    and evans_density: "evans_compact_support_w1p_zero_density_claim"
    and exponent_lower: "1 < p"
    and exponent_upper: "p < 2"
    and loss_positive: "0 < epsilon"
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
        aim_complex_lp_on_plane p coefficient \<and>
        {x. coefficient x \<noteq> 0} \<subseteq> Y
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
            (C * tau powr (-(1 - 1 / p) + epsilon) *
              (aim_complex_lp_norm p coefficient +
                Real_Vector_Spaces.norm
                  (slp_dbar_inverse coefficient c))))"
proof -
  obtain Cq :: real where Cq_positive: "0 < Cq"
    and coefficient_endpoint:
      "\<forall>tau c coefficient.
        2 \<le> tau \<and>
        (\<forall>y. y \<in> X \<longrightarrow>
          Real_Vector_Spaces.norm (y - c) \<le> R) \<and>
        aim_complex_lp_on_plane p coefficient \<and>
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
            (Cq * tau powr (-(1 - 1 / p) + epsilon) *
              aim_complex_lp_norm p coefficient)"
    using slp_left_initial_cauchy_source_esssup_power_loss_bound[
      OF riesz_hls cauchy_test_left_inverse evans_density exponent_lower
        exponent_upper loss_positive radius_nonnegative radius_lower
        set_radius X_open X_bounded Y_bounded cutoff_test cutoff_bound
        cutoff_derivative_zero_bound cutoff_derivative_one_bound
        A0_nonnegative B0_nonnegative B1_nonnegative]
    by blast
  obtain Cc :: real where Cc_positive: "0 < Cc"
    and center_endpoint:
      "\<forall>tau c center_value.
        2 \<le> tau \<and>
        (\<forall>y. y \<in> X \<longrightarrow>
          Real_Vector_Spaces.norm (y - c) \<le> R)
        \<longrightarrow>
        (\<lambda>z :: slp_point.
          ereal (Real_Vector_Spaces.norm
            (slp_restrict_field X
              (slp_partial_psi_inverse tau c
                (\<lambda>x. cutoff x * center_value)) z)))
          \<in> borel_measurable (lborel :: slp_point measure)
        \<and>
        esssup (lborel :: slp_point measure)
          (\<lambda>z :: slp_point.
            ereal (Real_Vector_Spaces.norm
              (slp_restrict_field X
                (slp_partial_psi_inverse tau c
                  (\<lambda>x. cutoff x * center_value)) z)))
          \<le> ereal
            (Cc * tau powr (-(1 - 1 / p) + epsilon) *
              Real_Vector_Spaces.norm center_value)"
    using slp_left_initial_center_value_esssup_power_loss_bound[
      OF riesz_hls cauchy_test_left_inverse exponent_lower exponent_upper
        loss_positive radius_nonnegative radius_lower set_radius X_open
        X_bounded cutoff_test]
    by blast
  obtain H :: real where H_positive: "0 < H"
    and two_cauchy:
      "\<forall>tau1 tau2 c1 c2 f outer inner.
        aim_complex_lp_on_plane p f \<longrightarrow>
        slp_cauchy_transform outer
          (slp_oscillatory_modulation tau1 c1
            (\<lambda>y. cutoff y * slp_cauchy_transform inner
              (slp_oscillatory_modulation tau2 c2 f) y))
          \<in> borel_measurable lborel \<and>
        (\<forall>z\<in>X.
          slp_cauchy_integrable_at outer
            (slp_oscillatory_modulation tau1 c1
              (\<lambda>y. cutoff y * slp_cauchy_transform inner
                (slp_oscillatory_modulation tau2 c2 f) y)) z \<and>
          Real_Vector_Spaces.norm (slp_cauchy_transform outer
            (slp_oscillatory_modulation tau1 c1
              (\<lambda>y. cutoff y * slp_cauchy_transform inner
                (slp_oscillatory_modulation tau2 c2 f) y)) z)
            \<le> H * aim_complex_lp_norm p f)"
    using slp_two_oscillatory_cauchy_test_cutoff_bound[
      OF exponent_lower exponent_upper X_bounded cutoff_test]
    by blast
  let ?FinalC = "Cq + Cc"
  have C_positive: "0 < ?FinalC"
    using Cq_positive Cc_positive by linarith
  have X_measurable: "X \<in> sets lborel"
    using X_open by simp
  have cutoff_plane: "slp_test_function_on UNIV cutoff"
    using cutoff_test unfolding slp_test_function_on_def by auto

  show ?thesis
  proof (rule exI[of _ ?FinalC], rule conjI[OF C_positive])
    show "\<forall>tau c coefficient.
        2 \<le> tau \<and>
        (\<forall>y. y \<in> X \<longrightarrow>
          Real_Vector_Spaces.norm (y - c) \<le> R) \<and>
        aim_complex_lp_on_plane p coefficient \<and>
        {x. coefficient x \<noteq> 0} \<subseteq> Y
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
            (?FinalC * tau powr (-(1 - 1 / p) + epsilon) *
              (aim_complex_lp_norm p coefficient +
                Real_Vector_Spaces.norm
                  (slp_dbar_inverse coefficient c)))"
    proof (intro allI impI)
      fix tau :: real and c :: slp_point
        and coefficient :: slp_scalar_field
      assume data:
        "2 \<le> tau \<and>
          (\<forall>y. y \<in> X \<longrightarrow>
            Real_Vector_Spaces.norm (y - c) \<le> R) \<and>
          aim_complex_lp_on_plane p coefficient \<and>
          {x. coefficient x \<noteq> 0} \<subseteq> Y"
      let ?primitive = "slp_dbar_inverse coefficient"
      let ?first =
        "slp_partial_psi_inverse tau c
          (\<lambda>x. cutoff x * ?primitive x)"
      let ?second =
        "slp_partial_psi_inverse tau c
          (\<lambda>x. cutoff x * ?primitive c)"
      let ?base =
        "slp_left_neumann_base tau c cutoff coefficient SLP_Dbar_Inverse"
      let ?rate = "tau powr (-(1 - 1 / p) + epsilon)"
      let ?qnorm = "aim_complex_lp_norm p coefficient"
      let ?anorm = "Real_Vector_Spaces.norm (?primitive c)"
      let ?h =
        "\<lambda>z :: slp_point.
          ereal (Real_Vector_Spaces.norm
            (slp_restrict_field X ?base z))"
      let ?hq =
        "\<lambda>z :: slp_point.
          ereal (Real_Vector_Spaces.norm
            (slp_restrict_field X ?first z))"
      let ?hc =
        "\<lambda>z :: slp_point.
          ereal (Real_Vector_Spaces.norm
            (slp_restrict_field X ?second z))"
      have coefficient_lp: "aim_complex_lp_on_plane p coefficient"
        using data by blast
      have coefficient_data:
          "?hq \<in> borel_measurable (lborel :: slp_point measure) \<and>
            esssup (lborel :: slp_point measure) ?hq \<le>
              ereal (Cq * ?rate * ?qnorm)"
        by (rule coefficient_endpoint[rule_format, OF data])
      have center_data:
          "?hc \<in> borel_measurable (lborel :: slp_point measure) \<and>
            esssup (lborel :: slp_point measure) ?hc \<le>
              ereal (Cc * ?rate * ?anorm)"
      proof (rule center_endpoint[rule_format, of tau c "?primitive c"])
        show "2 \<le> tau \<and>
            (\<forall>y. y \<in> X \<longrightarrow>
              Real_Vector_Spaces.norm (y - c) \<le> R)"
          using data by blast
      qed
      have zero_modulation:
          "slp_oscillatory_modulation 0 c coefficient = coefficient"
        by (rule ext)
          (simp add: slp_oscillatory_modulation_def slp_center_kernel_def)
      have first_transform_data:
          "?first \<in> borel_measurable lborel \<and>
            (\<forall>z\<in>X.
              slp_cauchy_integrable_at SLP_Partial_Inverse
                (slp_oscillatory_modulation tau c
                  (\<lambda>x. cutoff x * ?primitive x)) z \<and>
              Real_Vector_Spaces.norm (?first z) \<le> H * ?qnorm)"
      proof -
        have raw:
            "slp_cauchy_transform SLP_Partial_Inverse
              (slp_oscillatory_modulation tau c
                (\<lambda>y. cutoff y *
                  slp_cauchy_transform SLP_Dbar_Inverse
                    (slp_oscillatory_modulation 0 c coefficient) y))
              \<in> borel_measurable lborel \<and>
              (\<forall>z\<in>X.
                slp_cauchy_integrable_at SLP_Partial_Inverse
                  (slp_oscillatory_modulation tau c
                    (\<lambda>y. cutoff y *
                      slp_cauchy_transform SLP_Dbar_Inverse
                        (slp_oscillatory_modulation 0 c coefficient) y)) z
                \<and>
                Real_Vector_Spaces.norm
                  (slp_cauchy_transform SLP_Partial_Inverse
                    (slp_oscillatory_modulation tau c
                      (\<lambda>y. cutoff y *
                        slp_cauchy_transform SLP_Dbar_Inverse
                          (slp_oscillatory_modulation 0 c coefficient) y)) z)
                  \<le> H * ?qnorm)"
          by (rule two_cauchy[rule_format, OF coefficient_lp])
        show ?thesis
          using raw unfolding slp_partial_psi_inverse_def zero_modulation .
      qed
      have center_source_test:
          "slp_test_function_on UNIV (\<lambda>x. cutoff x * ?primitive c)"
      proof -
        have "slp_test_function_on UNIV
            (\<lambda>x. ?primitive c * cutoff x)"
          by (rule slp_test_function_on_mult_left[OF
                smooth_on_const cutoff_plane])
        then show ?thesis by (simp add: mult.commute)
      qed
      have center_modulated_test:
          "slp_test_function_on UNIV
            (slp_oscillatory_modulation tau c
              (\<lambda>x. cutoff x * ?primitive c))"
        unfolding slp_oscillatory_modulation_def
        by (rule slp_test_function_on_mult_left[OF
              slp_center_kernel_smooth center_source_test])
      have second_integrable:
          "\<And>z. slp_cauchy_integrable_at SLP_Partial_Inverse
            (slp_oscillatory_modulation tau c
              (\<lambda>x. cutoff x * ?primitive c)) z"
        by (rule slp_test_function_cauchy_integrable_at[OF
              center_modulated_test])
      have center_source_lp:
          "aim_complex_lp_on_plane 3 (\<lambda>x. cutoff x * ?primitive c)"
        by (rule slp_test_function_aim_complex_lp_on_plane[
              OF _ center_source_test]) simp
      have center_modulated_lp:
          "aim_complex_lp_on_plane 3
            (slp_oscillatory_modulation tau c
              (\<lambda>x. cutoff x * ?primitive c))"
        using center_source_lp by simp
      have center_source_support_bounded:
          "bounded {x. cutoff x * ?primitive c \<noteq> 0}"
      proof -
        have compact_support:
            "compact (closure {x. cutoff x * ?primitive c \<noteq> 0})"
          using center_source_test
          unfolding slp_test_function_on_def by blast
        show ?thesis
        proof (rule bounded_subset[OF compact_imp_bounded[OF compact_support]])
          show "{x. cutoff x * ?primitive c \<noteq> 0} \<subseteq>
              closure {x. cutoff x * ?primitive c \<noteq> 0}"
            by auto
        qed
      qed
      have center_modulated_support_bounded:
          "bounded {x. slp_oscillatory_modulation tau c
            (\<lambda>y. cutoff y * ?primitive c) x \<noteq> 0}"
        using center_source_support_bounded by simp
      have second_transform_measurable:
          "?second \<in> borel_measurable lborel"
        unfolding slp_partial_psi_inverse_def
        by (rule slp_cauchy_transform_measurable_above_two_bounded_support[
              where r=3, OF _ center_modulated_lp
                center_modulated_support_bounded]) simp

      have base_pointwise:
          "?base z = ?first z - ?second z" if z_in: "z \<in> X" for z
      proof -
        let ?u =
          "slp_oscillatory_modulation tau c
            (\<lambda>x. cutoff x * ?primitive x)"
        let ?v =
          "slp_oscillatory_modulation tau c
            (\<lambda>x. cutoff x * ?primitive c)"
        let ?negative_v = "\<lambda>x. (- 1) * ?v x"
        let ?difference = "\<lambda>x. ?u x + ?negative_v x"
        let ?literal =
          "slp_oscillatory_modulation tau c
            (\<lambda>x. cutoff x * (?primitive x - ?primitive c))"
        have first_integrable:
            "slp_cauchy_integrable_at SLP_Partial_Inverse ?u z"
          using first_transform_data z_in by blast
        have second_integrable_at:
            "slp_cauchy_integrable_at SLP_Partial_Inverse ?v z"
          by (rule second_integrable)
        have negative_integrable:
            "slp_cauchy_integrable_at SLP_Partial_Inverse ?negative_v z"
          by (rule slp_cauchy_integrable_at_mult_left[OF
                second_integrable_at])
        have difference_integrable:
            "slp_cauchy_integrable_at SLP_Partial_Inverse ?difference z"
          by (rule slp_cauchy_integrable_at_add[OF
                first_integrable negative_integrable])
        have literal_eq: "?literal = ?difference"
          by (rule ext)
            (simp add: slp_oscillatory_modulation_def algebra_simps)
        have literal_integrable:
            "slp_cauchy_integrable_at SLP_Partial_Inverse ?literal z"
          unfolding literal_eq by (rule difference_integrable)
        have congruent:
            "slp_cauchy_transform SLP_Partial_Inverse ?literal z =
              slp_cauchy_transform SLP_Partial_Inverse ?difference z"
        proof (rule slp_cauchy_transform_cong_ae[
              OF literal_integrable difference_integrable])
          show "AE x in (lborel :: slp_point measure).
              ?literal x = ?difference x"
            by (rule AE_I2) (simp only: literal_eq)
        qed
        have additive:
            "slp_cauchy_transform SLP_Partial_Inverse ?difference z =
              slp_cauchy_transform SLP_Partial_Inverse ?u z +
                slp_cauchy_transform SLP_Partial_Inverse ?negative_v z"
          by (rule slp_cauchy_transform_add[
                OF first_integrable negative_integrable])
        have negative:
            "slp_cauchy_transform SLP_Partial_Inverse ?negative_v z =
              (- 1) * slp_cauchy_transform SLP_Partial_Inverse ?v z"
          by (rule slp_cauchy_transform_mult_left[OF second_integrable_at])
        show ?thesis
          using congruent additive negative
          unfolding slp_left_neumann_base_def
            slp_partial_psi_inverse_def by simp
      qed
      have restricted_eq:
          "slp_restrict_field X ?base =
            (\<lambda>z. slp_restrict_field X ?first z -
              slp_restrict_field X ?second z)"
      proof (rule ext)
        fix z
        show "slp_restrict_field X ?base z =
            slp_restrict_field X ?first z -
              slp_restrict_field X ?second z"
        proof (cases "z \<in> X")
          case True
          then show ?thesis
            using base_pointwise[OF True]
            by (simp add: slp_restrict_field_def)
        next
          case False
          then show ?thesis by (simp add: slp_restrict_field_def)
        qed
      qed
      have first_restricted_measurable:
          "slp_restrict_field X ?first \<in> borel_measurable lborel"
        by (rule slp_restrict_field_measurable[
              OF X_measurable conjunct1[OF first_transform_data]])
      have second_restricted_measurable:
          "slp_restrict_field X ?second \<in> borel_measurable lborel"
        by (rule slp_restrict_field_measurable[
              OF X_measurable second_transform_measurable])
      have base_restricted_measurable:
          "slp_restrict_field X ?base \<in> borel_measurable lborel"
        unfolding restricted_eq
        using first_restricted_measurable second_restricted_measurable
        by measurable
      have h_measurable:
          "?h \<in> borel_measurable (lborel :: slp_point measure)"
        using base_restricted_measurable by measurable
      have pointwise_norm_bound: "?h z \<le> ?hq z + ?hc z" for z
      proof -
        have norm_bound:
            "Real_Vector_Spaces.norm (slp_restrict_field X ?base z) \<le>
              Real_Vector_Spaces.norm (slp_restrict_field X ?first z) +
                Real_Vector_Spaces.norm (slp_restrict_field X ?second z)"
          using norm_triangle_ineq[
            of "slp_restrict_field X ?first z"
              "- slp_restrict_field X ?second z"]
          by (simp only: restricted_eq diff_conv_add_uminus norm_minus_cancel)
        show ?thesis using norm_bound by simp
      qed
      have rate_nonnegative: "0 \<le> ?rate"
        by (rule powr_ge_zero)
      have qnorm_nonnegative: "0 \<le> ?qnorm"
        unfolding aim_complex_lp_norm_def by (rule powr_ge_zero)
      have anorm_nonnegative: "0 \<le> ?anorm"
        by simp
      have Cq_nonnegative: "0 \<le> Cq"
        using Cq_positive by linarith
      have Cc_nonnegative: "0 \<le> Cc"
        using Cc_positive by linarith
      have scalar_enlarged:
          "Cq * ?rate * ?qnorm + Cc * ?rate * ?anorm \<le>
            ?FinalC * ?rate * (?qnorm + ?anorm)"
      proof -
        have cross_nonnegative:
            "0 \<le> Cq * ?rate * ?anorm + Cc * ?rate * ?qnorm"
          by (intro add_nonneg_nonneg mult_nonneg_nonneg)
            (use Cq_nonnegative Cc_nonnegative rate_nonnegative
              qnorm_nonnegative anorm_nonnegative in simp_all)
        have identity:
            "?FinalC * ?rate * (?qnorm + ?anorm) -
                (Cq * ?rate * ?qnorm + Cc * ?rate * ?anorm) =
              Cq * ?rate * ?anorm + Cc * ?rate * ?qnorm"
          by (simp add: algebra_simps)
        show ?thesis using cross_nonnegative identity by linarith
      qed
      have target_esssup:
          "esssup (lborel :: slp_point measure) ?h \<le>
            ereal (?FinalC * ?rate * (?qnorm + ?anorm))"
      proof (rule order_trans)
        show "esssup (lborel :: slp_point measure) ?h \<le>
            esssup (lborel :: slp_point measure) (\<lambda>z. ?hq z + ?hc z)"
          by (rule esssup_mono[OF h_measurable pointwise_norm_bound])
        show "esssup (lborel :: slp_point measure) (\<lambda>z. ?hq z + ?hc z)
            \<le> ereal (?FinalC * ?rate * (?qnorm + ?anorm))"
        proof (rule order_trans[OF esssup_add])
          have endpoint_sum:
              "esssup (lborel :: slp_point measure) ?hq +
                  esssup (lborel :: slp_point measure) ?hc \<le>
                ereal (Cq * ?rate * ?qnorm) +
                  ereal (Cc * ?rate * ?anorm)"
            by (rule add_mono[OF conjunct2[OF coefficient_data]
                  conjunct2[OF center_data]])
          show "esssup (lborel :: slp_point measure) ?hq +
                esssup (lborel :: slp_point measure) ?hc \<le>
              ereal (?FinalC * ?rate * (?qnorm + ?anorm))"
            by (rule order_trans[OF endpoint_sum])
              (use scalar_enlarged in simp)
        qed
      qed
      show
          "(\<lambda>z :: slp_point.
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
              (?FinalC * tau powr (-(1 - 1 / p) + epsilon) *
                (aim_complex_lp_norm p coefficient +
                  Real_Vector_Spaces.norm
                    (slp_dbar_inverse coefficient c)))"
        by (rule conjI[OF h_measurable target_esssup])
    qed
  qed
qed

end

end
