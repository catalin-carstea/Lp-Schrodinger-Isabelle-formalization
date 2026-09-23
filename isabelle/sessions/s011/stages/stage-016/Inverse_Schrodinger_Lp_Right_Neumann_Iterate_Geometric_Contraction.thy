theory Inverse_Schrodinger_Lp_Right_Neumann_Iterate_Geometric_Contraction
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_016.Inverse_Schrodinger_Lp_Nested_Coefficient_Product_Right_Contraction"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_015.Inverse_Schrodinger_Lp_Left_Neumann_Iterate_Geometric_Contraction"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_014.Inverse_Schrodinger_Lp_Exact_Neumann_Iterate_Bridge"
begin

hide_const (open) Commutative_Ring.norm
section \<open>Concrete geometric control of every right Neumann iterate\<close>

context slp_cauchy_local_w1s
begin

theorem slp_right_neumann_iterate_restricted_esssup_geometric:
  fixes p epsilon A R A0 B0 B1 M :: real
    and X :: "slp_point set"
    and cutoff coefficient initial :: slp_scalar_field
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
    and initial_measurable: "initial \<in> borel_measurable lborel"
    and initial_bound:
      "AE x in lborel. Real_Vector_Spaces.norm (initial x) \<le> M"
    and M_nonnegative: "0 \<le> M"
  shows
    "\<exists>T::real. 2 \<le> T \<and>
      (\<forall>tau c.
        T \<le> tau \<and>
        (\<forall>y. y \<in> X \<longrightarrow>
          Real_Vector_Spaces.norm (y - c) \<le> R)
        \<longrightarrow>
        (\<forall>j.
          slp_restrict_field X
              (slp_neumann_iterate
                (slp_right_neumann_step tau c cutoff coefficient)
                initial j)
            \<in> borel_measurable lborel
          \<and>
          (\<lambda>z :: slp_point.
            ereal (Real_Vector_Spaces.norm
              (slp_restrict_field X
                (slp_neumann_iterate
                  (slp_right_neumann_step tau c cutoff coefficient)
                  initial j) z)))
            \<in> borel_measurable (lborel :: slp_point measure)
          \<and>
          esssup (lborel :: slp_point measure)
            (\<lambda>z :: slp_point.
              ereal (Real_Vector_Spaces.norm
                (slp_restrict_field X
                  (slp_neumann_iterate
                    (slp_right_neumann_step tau c cutoff coefficient)
                    initial j) z)))
            \<le> ereal (M * (1 / 2) ^ j)
          \<and>
          (AE z in lborel.
            Real_Vector_Spaces.norm
              (slp_restrict_field X
                (slp_neumann_iterate
                  (slp_right_neumann_step tau c cutoff coefficient)
                  initial j) z)
              \<le> M * (1 / 2) ^ j)))"
proof -
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
      then show ?thesis
        by (simp add: slp_restrict_field_def)
    next
      case False
      then have "coefficient y = 0"
        using coefficient_support by auto
      then show ?thesis by simp
    qed
  qed
  have step_restrict_eq:
      "slp_right_neumann_step tau c cutoff coefficient f =
        slp_right_neumann_step tau c cutoff coefficient
          (slp_restrict_field X f)"
    for tau :: real and c :: slp_point and f :: slp_scalar_field
    unfolding slp_right_neumann_step_def
    apply (subst source_restrict_eq)
    apply (rule refl)
    done

  obtain T :: real where T_lower: "2 \<le> T"
    and contraction:
      "\<forall>tau c multiplier N.
        T \<le> tau \<and>
        (\<forall>y. y \<in> X \<longrightarrow>
          Real_Vector_Spaces.norm (y - c) \<le> R) \<and>
        multiplier \<in> borel_measurable lborel \<and>
        (AE x in lborel. Real_Vector_Spaces.norm (multiplier x) \<le> N) \<and>
        0 \<le> N
        \<longrightarrow>
        (\<lambda>z :: slp_point.
          ereal (Real_Vector_Spaces.norm
            (slp_restrict_field X
              (slp_right_neumann_step tau c cutoff coefficient multiplier) z)))
          \<in> borel_measurable (lborel :: slp_point measure)
        \<and>
        esssup (lborel :: slp_point measure)
          (\<lambda>z :: slp_point.
            ereal (Real_Vector_Spaces.norm
              (slp_restrict_field X
                (slp_right_neumann_step tau c cutoff coefficient multiplier) z)))
          \<le> ereal ((1 / 2) * N)"
    using slp_nested_coefficient_product_right_esssup_contraction[
        OF riesz_hls cauchy_test_left_inverse evans_density
          exponent_lower exponent_upper loss_positive loss_upper
          radius_nonnegative radius_lower set_radius X_open X_bounded
          X_bounded cutoff_test cutoff_bound cutoff_derivative_zero_bound
          cutoff_derivative_one_bound A0_nonnegative B0_nonnegative
          B1_nonnegative coefficient_lp coefficient_support]
    unfolding slp_right_neumann_step_def
    by blast

  obtain C :: real where C_positive: "0 < C"
    and two_cauchy:
      "\<forall>tau1 tau2 c1 c2 f outer inner.
        aim_complex_lp_on_plane p f \<longrightarrow>
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
          Real_Vector_Spaces.norm
            (slp_cauchy_transform outer
              (slp_oscillatory_modulation tau1 c1
                (\<lambda>y. cutoff y * slp_cauchy_transform inner
                  (slp_oscillatory_modulation tau2 c2 f) y)) z)
            \<le> C * aim_complex_lp_norm p f)"
    using slp_two_oscillatory_cauchy_test_cutoff_bound[
        OF exponent_lower exponent_upper X_bounded cutoff_test]
    by blast

  show ?thesis
  proof (rule exI[of _ T], rule conjI[OF T_lower])
    show
      "\<forall>tau c.
        T \<le> tau \<and>
        (\<forall>y. y \<in> X \<longrightarrow>
          Real_Vector_Spaces.norm (y - c) \<le> R)
        \<longrightarrow>
        (\<forall>j.
          slp_restrict_field X
              (slp_neumann_iterate
                (slp_right_neumann_step tau c cutoff coefficient)
                initial j)
            \<in> borel_measurable lborel
          \<and>
          (\<lambda>z :: slp_point.
            ereal (Real_Vector_Spaces.norm
              (slp_restrict_field X
                (slp_neumann_iterate
                  (slp_right_neumann_step tau c cutoff coefficient)
                  initial j) z)))
            \<in> borel_measurable (lborel :: slp_point measure)
          \<and>
          esssup (lborel :: slp_point measure)
            (\<lambda>z :: slp_point.
              ereal (Real_Vector_Spaces.norm
                (slp_restrict_field X
                  (slp_neumann_iterate
                    (slp_right_neumann_step tau c cutoff coefficient)
                    initial j) z)))
            \<le> ereal (M * (1 / 2) ^ j)
          \<and>
          (AE z in lborel.
            Real_Vector_Spaces.norm
              (slp_restrict_field X
                (slp_neumann_iterate
                  (slp_right_neumann_step tau c cutoff coefficient)
                  initial j) z)
              \<le> M * (1 / 2) ^ j))"
    proof (rule allI, rule allI, rule impI)
      fix tau :: real and c :: slp_point
      assume threshold_geometry:
        "T \<le> tau \<and>
          (\<forall>y. y \<in> X \<longrightarrow>
            Real_Vector_Spaces.norm (y - c) \<le> R)"
      then have tau_lower: "T \<le> tau"
        and center_geometry:
          "\<forall>y. y \<in> X \<longrightarrow>
            Real_Vector_Spaces.norm (y - c) \<le> R"
        by blast+
      have all_iterates:
        "\<forall>j.
          slp_restrict_field X
              (slp_neumann_iterate
                (slp_right_neumann_step tau c cutoff coefficient)
                initial j)
            \<in> borel_measurable lborel
          \<and>
          (\<lambda>z :: slp_point.
            ereal (Real_Vector_Spaces.norm
              (slp_restrict_field X
                (slp_neumann_iterate
                  (slp_right_neumann_step tau c cutoff coefficient)
                  initial j) z)))
            \<in> borel_measurable (lborel :: slp_point measure)
          \<and>
          esssup (lborel :: slp_point measure)
            (\<lambda>z :: slp_point.
              ereal (Real_Vector_Spaces.norm
                (slp_restrict_field X
                  (slp_neumann_iterate
                    (slp_right_neumann_step tau c cutoff coefficient)
                    initial j) z)))
            \<le> ereal (M * (1 / 2) ^ j)
          \<and>
          (AE z in lborel.
            Real_Vector_Spaces.norm
              (slp_restrict_field X
                (slp_neumann_iterate
                  (slp_right_neumann_step tau c cutoff coefficient)
                  initial j) z)
              \<le> M * (1 / 2) ^ j)"
      proof
        fix j :: nat
        show
          "slp_restrict_field X
              (slp_neumann_iterate
                (slp_right_neumann_step tau c cutoff coefficient)
                initial j)
            \<in> borel_measurable lborel
          \<and>
          (\<lambda>z :: slp_point.
            ereal (Real_Vector_Spaces.norm
              (slp_restrict_field X
                (slp_neumann_iterate
                  (slp_right_neumann_step tau c cutoff coefficient)
                  initial j) z)))
            \<in> borel_measurable (lborel :: slp_point measure)
          \<and>
          esssup (lborel :: slp_point measure)
            (\<lambda>z :: slp_point.
              ereal (Real_Vector_Spaces.norm
                (slp_restrict_field X
                  (slp_neumann_iterate
                    (slp_right_neumann_step tau c cutoff coefficient)
                    initial j) z)))
            \<le> ereal (M * (1 / 2) ^ j)
          \<and>
          (AE z in lborel.
            Real_Vector_Spaces.norm
              (slp_restrict_field X
                (slp_neumann_iterate
                  (slp_right_neumann_step tau c cutoff coefficient)
                  initial j) z)
              \<le> M * (1 / 2) ^ j)"
        proof (induction j)
          case 0
          let ?u = "slp_restrict_field X initial"
          have u_measurable: "?u \<in> borel_measurable lborel"
            by (rule slp_restrict_field_measurable[
                  OF X_measurable initial_measurable])
          have u_norm_measurable:
              "(\<lambda>z :: slp_point.
                ereal (Real_Vector_Spaces.norm (?u z)))
                \<in> borel_measurable (lborel :: slp_point measure)"
            using u_measurable by measurable
          have u_AE:
              "AE z in lborel. Real_Vector_Spaces.norm (?u z) \<le> M"
            using initial_bound
          proof eventually_elim
            fix z :: slp_point
            assume at_z:
              "Real_Vector_Spaces.norm (initial z) \<le> M"
            show "Real_Vector_Spaces.norm (?u z) \<le> M"
            proof (cases "z \<in> X")
              case True
              then show ?thesis
                using at_z by (simp add: slp_restrict_field_def)
            next
              case False
              then show ?thesis
                using M_nonnegative by (simp add: slp_restrict_field_def)
            qed
          qed
          have u_ereal_AE:
              "AE z in lborel.
                ereal (Real_Vector_Spaces.norm (?u z)) \<le> ereal M"
            using u_AE by eventually_elim simp
          have u_esssup:
              "esssup (lborel :: slp_point measure)
                  (\<lambda>z :: slp_point.
                    ereal (Real_Vector_Spaces.norm (?u z)))
                \<le> ereal M"
            by (rule esssup_I[OF u_norm_measurable u_ereal_AE])
          show ?case
            using u_measurable u_norm_measurable u_esssup u_AE
            by (simp only: slp_neumann_iterate_zero power_0 mult_1_right)
        next
          case (Suc j)
          let ?u =
            "slp_restrict_field X
              (slp_neumann_iterate
                (slp_right_neumann_step tau c cutoff coefficient)
                initial j)"
          let ?N = "M * (1 / 2) ^ j"
          let ?v =
            "slp_restrict_field X
              (slp_neumann_iterate
                (slp_right_neumann_step tau c cutoff coefficient)
                initial (Suc j))"
          have u_measurable: "?u \<in> borel_measurable lborel"
            using Suc.IH by blast
          have u_AE:
              "AE z in lborel. Real_Vector_Spaces.norm (?u z) \<le> ?N"
            using Suc.IH by blast
          have N_nonnegative: "0 \<le> ?N"
            by (rule mult_nonneg_nonneg[OF M_nonnegative]) simp
          have successor_restrict:
              "?v = slp_restrict_field X
                (slp_right_neumann_step tau c cutoff coefficient ?u)"
            unfolding slp_neumann_iterate_Suc
            apply (subst step_restrict_eq)
            apply (rule refl)
            done
          have contract_data:
              "(\<lambda>z :: slp_point.
                ereal (Real_Vector_Spaces.norm
                  (slp_restrict_field X
                    (slp_right_neumann_step tau c cutoff coefficient ?u) z)))
                \<in> borel_measurable (lborel :: slp_point measure)
              \<and>
              esssup (lborel :: slp_point measure)
                (\<lambda>z :: slp_point.
                  ereal (Real_Vector_Spaces.norm
                    (slp_restrict_field X
                      (slp_right_neumann_step tau c cutoff coefficient ?u) z)))
                \<le> ereal ((1 / 2) * ?N)"
            using contraction tau_lower center_geometry u_measurable u_AE
              N_nonnegative by blast
          have p_positive: "0 < p"
            using exponent_lower by linarith
          have product_lp:
              "aim_complex_lp_on_plane p
                (\<lambda>x. ?u x * coefficient x)"
            by (rule slp_complex_lp_AE_bounded_multiplier(1)[
                  OF p_positive u_measurable u_AE N_nonnegative
                    coefficient_lp])
          have source_lp:
              "aim_complex_lp_on_plane p
                (\<lambda>x. coefficient x * ?u x)"
            using product_lp by (simp only: mult.commute)
          have step_measurable:
              "slp_right_neumann_step tau c cutoff coefficient ?u
                \<in> borel_measurable lborel"
            using two_cauchy source_lp
            by (simp only: slp_right_neumann_step_def
                slp_partial_psi_inverse_def slp_dbar_psi_inverse_def; blast)
          have v_measurable: "?v \<in> borel_measurable lborel"
            unfolding successor_restrict
            by (rule slp_restrict_field_measurable[
                  OF X_measurable step_measurable])
          have half_normalization:
              "(1 / 2) * ?N = M * (1 / 2) ^ Suc j"
            by (simp add: power_Suc algebra_simps)
          have v_norm_measurable:
              "(\<lambda>z :: slp_point.
                ereal (Real_Vector_Spaces.norm (?v z)))
                \<in> borel_measurable (lborel :: slp_point measure)"
            using conjunct1[OF contract_data]
            unfolding successor_restrict .
          have v_esssup:
              "esssup (lborel :: slp_point measure)
                  (\<lambda>z :: slp_point.
                    ereal (Real_Vector_Spaces.norm (?v z)))
                \<le> ereal (M * (1 / 2) ^ Suc j)"
            using conjunct2[OF contract_data]
            unfolding successor_restrict half_normalization .
          have v_AE:
              "AE z in lborel.
                Real_Vector_Spaces.norm (?v z) \<le>
                  M * (1 / 2) ^ Suc j"
            by (rule slp_ereal_norm_esssup_bound_imp_AE[
                  OF v_norm_measurable v_esssup])
          show ?case
            using v_measurable v_norm_measurable v_esssup v_AE by blast
        qed
      qed
      show
        "\<forall>j.
          slp_restrict_field X
              (slp_neumann_iterate
                (slp_right_neumann_step tau c cutoff coefficient)
                initial j)
            \<in> borel_measurable lborel
          \<and>
          (\<lambda>z :: slp_point.
            ereal (Real_Vector_Spaces.norm
              (slp_restrict_field X
                (slp_neumann_iterate
                  (slp_right_neumann_step tau c cutoff coefficient)
                  initial j) z)))
            \<in> borel_measurable (lborel :: slp_point measure)
          \<and>
          esssup (lborel :: slp_point measure)
            (\<lambda>z :: slp_point.
              ereal (Real_Vector_Spaces.norm
                (slp_restrict_field X
                  (slp_neumann_iterate
                    (slp_right_neumann_step tau c cutoff coefficient)
                    initial j) z)))
            \<le> ereal (M * (1 / 2) ^ j)
          \<and>
          (AE z in lborel.
            Real_Vector_Spaces.norm
              (slp_restrict_field X
                (slp_neumann_iterate
                  (slp_right_neumann_step tau c cutoff coefficient)
                  initial j) z)
              \<le> M * (1 / 2) ^ j)"
        by (rule all_iterates)
    qed
  qed
qed

end

end
