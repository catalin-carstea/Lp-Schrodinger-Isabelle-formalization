theory Inverse_Schrodinger_Lp_Left_Initial_Cauchy_Source_Power_Loss
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_015.Inverse_Schrodinger_Lp_Left_Initial_Cauchy_Source_Endpoints"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_015.Inverse_Schrodinger_Lp_Nested_Coefficient_Product_Power_Loss_Esssup"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Initial Cauchy-source power-loss bound\<close>

context slp_cauchy_local_w1s
begin

theorem slp_left_initial_cauchy_source_esssup_power_loss_bound:
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
            (C * tau powr (-(1 - 1 / p) + epsilon) *
              aim_complex_lp_norm p coefficient))"
proof -
  obtain C :: real where C_positive: "0 < C"
    and endpoint:
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
            (C * M * tau powr (-(1 - 1 / p) + epsilon) *
              aim_complex_lp_norm p coefficient)"
    using slp_nested_coefficient_product_left_esssup_power_loss_bound[
      OF riesz_hls cauchy_test_left_inverse evans_density exponent_lower
        exponent_upper loss_positive radius_nonnegative radius_lower
        set_radius X_open X_bounded Y_bounded cutoff_test cutoff_bound
        cutoff_derivative_zero_bound cutoff_derivative_one_bound
        A0_nonnegative B0_nonnegative B1_nonnegative]
    by blast
  show ?thesis
  proof (rule exI[of _ C], rule conjI[OF C_positive])
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
            (C * tau powr (-(1 - 1 / p) + epsilon) *
              aim_complex_lp_norm p coefficient)"
    proof (intro allI impI)
      fix tau :: real and c :: slp_point and coefficient :: slp_scalar_field
      assume data:
        "2 \<le> tau \<and>
          (\<forall>y. y \<in> X \<longrightarrow>
            Real_Vector_Spaces.norm (y - c) \<le> R) \<and>
          aim_complex_lp_on_plane p coefficient \<and>
          {x. coefficient x \<noteq> 0} \<subseteq> Y"
      let ?modulated = "slp_oscillatory_modulation tau c coefficient"
      let ?one = "\<lambda>_ :: slp_point. (1 :: complex)"
      have modulated_lp: "aim_complex_lp_on_plane p ?modulated"
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
          "aim_complex_lp_norm p ?modulated =
            aim_complex_lp_norm p coefficient"
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
              (C * 1 * tau powr (-(1 - 1 / p) + epsilon) *
                aim_complex_lp_norm p ?modulated)"
      proof (rule endpoint[rule_format, of tau c ?modulated ?one 1])
        show "2 \<le> tau \<and>
            (\<forall>y. y \<in> X \<longrightarrow>
              Real_Vector_Spaces.norm (y - c) \<le> R) \<and>
            aim_complex_lp_on_plane p ?modulated \<and>
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
              (C * tau powr (-(1 - 1 / p) + epsilon) *
                aim_complex_lp_norm p coefficient)"
        using raw unfolding inner_cancel modulated_norm by simp
    qed
  qed
qed

end

end
