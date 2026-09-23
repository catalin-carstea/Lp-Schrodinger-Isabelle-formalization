theory Inverse_Schrodinger_Lp_Right_Neumann_Joint_Geometric_Series
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_016.Inverse_Schrodinger_Lp_Right_Neumann_Iterate_Lpstar_Geometric"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_016.Inverse_Schrodinger_Lp_Right_Neumann_Iterate_Joint_Measurable"
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_016.Inverse_Schrodinger_Lp_Joint_Fiber_Geometric_Series"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Literal right Neumann series on a measurable center carrier\<close>

context slp_cauchy_local_w1s
begin

theorem slp_right_neumann_joint_geometric_series:
  fixes p epsilon A R A0 B0 B1 :: real
    and X centers :: "slp_point set"
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
    and centers_measurable: "centers \<in> sets lborel"
    and centers_nonempty: "centers \<noteq> {}"
    and center_geometry:
      "\<And>c y. c \<in> centers \<Longrightarrow> y \<in> X \<Longrightarrow>
        Real_Vector_Spaces.norm (y - c) \<le> R"
  shows
    "\<exists>C CV T::real. 0 < C \<and> 0 < CV \<and> 2 \<le> T \<and>
      (\<forall>tau. T \<le> tau \<longrightarrow>
        (let rho = CV * tau powr (-(1 - 1 / p) + epsilon);
             majorant = (\<lambda>c.
               if c \<in> centers
               then C * tau powr (-(1 - 1 / p) + epsilon) *
                 (aim_complex_lp_norm p coefficient +
                   Real_Vector_Spaces.norm (slp_partial_inverse coefficient c))
               else 0);
             U = (\<lambda>j c z.
               if c \<in> centers
               then slp_restrict_field X
                 (slp_neumann_iterate
                   (slp_right_neumann_step tau c cutoff coefficient)
                   (slp_right_neumann_base tau c cutoff coefficient
                     SLP_Partial_Inverse) j) z
               else 0)
         in rho \<le> 1 / 2
          \<and> (AE pair in lborel \<Otimes>\<^sub>M lborel. \<forall>j.
            Real_Vector_Spaces.norm
              (U j (fst pair) (snd pair)) \<le>
              majorant (fst pair) * rho ^ j)
          \<and> (\<lambda>pair :: slp_point \<times> slp_point.
            \<Sum>j. U j (fst pair) (snd pair)) \<in>
              borel_measurable (lborel \<Otimes>\<^sub>M lborel)
          \<and> (AE pair in lborel \<Otimes>\<^sub>M lborel.
            summable (\<lambda>j.
              Real_Vector_Spaces.norm (U j (fst pair) (snd pair))))
          \<and> (AE pair in lborel \<Otimes>\<^sub>M lborel.
            summable (\<lambda>j. U j (fst pair) (snd pair)))
          \<and> (AE pair in lborel \<Otimes>\<^sub>M lborel.
            Real_Vector_Spaces.norm
              (\<Sum>j. U j (fst pair) (snd pair)) \<le>
              majorant (fst pair) / (1 - rho))))"
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

  have X_measurable: "X \<in> sets lborel"
    using X_open by simp
  have cutoff_smooth: "smooth_on UNIV cutoff"
    using cutoff_test unfolding slp_test_function_on_def by blast
  have cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    using borel_measurable_continuous_onI[
      OF smooth_on_imp_continuous_on[OF cutoff_smooth]] by simp
  have coefficient_measurable: "coefficient \<in> borel_measurable lborel"
    using coefficient_lp unfolding aim_complex_lp_on_plane_def by blast
  have dbar_measurable:
      "slp_partial_inverse coefficient \<in> borel_measurable lborel"
    by (rule slp_cauchy_transform_measurable_below_two[
          where orientation=SLP_Partial_Inverse and p=p,
          OF exponent_lower exponent_upper coefficient_lp])

  show ?thesis
  proof (rule exI[of _ C], rule exI[of _ CV], rule exI[of _ T],
      rule conjI[OF C_positive], rule conjI[OF CV_positive],
      rule conjI[OF threshold_lower])
    show
      "\<forall>tau. T \<le> tau \<longrightarrow>
        (let rho = CV * tau powr (-(1 - 1 / p) + epsilon);
             majorant = (\<lambda>c.
               if c \<in> centers
               then C * tau powr (-(1 - 1 / p) + epsilon) *
                 (aim_complex_lp_norm p coefficient +
                   Real_Vector_Spaces.norm (slp_partial_inverse coefficient c))
               else 0);
             U = (\<lambda>j c z.
               if c \<in> centers
               then slp_restrict_field X
                 (slp_neumann_iterate
                   (slp_right_neumann_step tau c cutoff coefficient)
                   (slp_right_neumann_base tau c cutoff coefficient
                     SLP_Partial_Inverse) j) z
               else 0)
         in rho \<le> 1 / 2
          \<and> (AE pair in lborel \<Otimes>\<^sub>M lborel. \<forall>j.
            Real_Vector_Spaces.norm
              (U j (fst pair) (snd pair)) \<le>
              majorant (fst pair) * rho ^ j)
          \<and> (\<lambda>pair :: slp_point \<times> slp_point.
            \<Sum>j. U j (fst pair) (snd pair)) \<in>
              borel_measurable (lborel \<Otimes>\<^sub>M lborel)
          \<and> (AE pair in lborel \<Otimes>\<^sub>M lborel.
            summable (\<lambda>j.
              Real_Vector_Spaces.norm (U j (fst pair) (snd pair))))
          \<and> (AE pair in lborel \<Otimes>\<^sub>M lborel.
            summable (\<lambda>j. U j (fst pair) (snd pair)))
          \<and> (AE pair in lborel \<Otimes>\<^sub>M lborel.
            Real_Vector_Spaces.norm
              (\<Sum>j. U j (fst pair) (snd pair)) \<le>
              majorant (fst pair) / (1 - rho)))"
    proof (intro allI impI)
      fix tau :: real
      assume tau_large: "T \<le> tau"
      let ?rho = "CV * tau powr (-(1 - 1 / p) + epsilon)"
      let ?majorant =
        "\<lambda>c. if c \<in> centers
          then C * tau powr (-(1 - 1 / p) + epsilon) *
            (aim_complex_lp_norm p coefficient +
              Real_Vector_Spaces.norm (slp_partial_inverse coefficient c))
          else 0"
      let ?U =
        "\<lambda>j c z. if c \<in> centers
          then slp_restrict_field X
            (slp_neumann_iterate
              (slp_right_neumann_step tau c cutoff coefficient)
              (slp_right_neumann_base tau c cutoff coefficient
                SLP_Partial_Inverse) j) z
          else 0"

      obtain c0 :: slp_point where c0_in: "c0 \<in> centers"
        using centers_nonempty by blast
      have c0_geometry:
          "\<forall>y. y \<in> X \<longrightarrow>
            Real_Vector_Spaces.norm (y - c0) \<le> R"
        using center_geometry[OF c0_in] by blast
      have rho_half: "?rho \<le> 1 / 2"
        using iterate_data[rule_format, of tau c0] tau_large c0_geometry
        by blast
      have rho_nonnegative: "0 \<le> ?rho"
        by (rule mult_nonneg_nonneg)
          (use CV_positive in linarith, rule powr_ge_zero)
      have rho_strict: "?rho < 1"
        using rho_half by linarith

      have majorant_measurable:
          "?majorant \<in> borel_measurable lborel"
        using centers_measurable dbar_measurable by measurable
      have majorant_nonnegative: "\<And>c. 0 \<le> ?majorant c"
      proof -
        fix c :: slp_point
        show "0 \<le> ?majorant c"
        proof (cases "c \<in> centers")
          case True
          have scale_nonnegative:
              "0 \<le> C * tau powr (-(1 - 1 / p) + epsilon)"
            by (rule mult_nonneg_nonneg)
              (use C_positive in linarith, rule powr_ge_zero)
          have datum_nonnegative:
              "0 \<le> aim_complex_lp_norm p coefficient +
                Real_Vector_Spaces.norm (slp_partial_inverse coefficient c)"
            unfolding aim_complex_lp_norm_def by simp
          show ?thesis
            using True mult_nonneg_nonneg[
              OF scale_nonnegative datum_nonnegative] by simp
        next
          case False
          then show ?thesis by simp
        qed
      qed

      have term_measurable:
          "\<And>j. (\<lambda>pair :: slp_point \<times> slp_point.
            ?U j (fst pair) (snd pair)) \<in>
              borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
      proof -
        fix j :: nat
        have totalized_iterate:
            "(\<lambda>pair :: slp_point \<times> slp_point.
              if fst pair \<in> (UNIV :: slp_point set)
              then slp_right_neumann_iterate j tau (fst pair) cutoff coefficient
                SLP_Partial_Inverse (snd pair)
              else 0) \<in>
                borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
          by (rule slp_right_neumann_iterate_conull_zero_joint_measurable[
                OF cutoff_measurable coefficient_measurable]) simp_all
        have abstract_iterate:
            "(\<lambda>pair :: slp_point \<times> slp_point.
              slp_neumann_iterate
                (slp_right_neumann_step tau (fst pair) cutoff coefficient)
                (slp_right_neumann_base tau (fst pair) cutoff coefficient
                  SLP_Partial_Inverse) j (snd pair)) \<in>
              borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
          using totalized_iterate
          by (simp only: UNIV_I if_True slp_right_neumann_iterate_eq_abstract)
        show
          "(\<lambda>pair :: slp_point \<times> slp_point.
            ?U j (fst pair) (snd pair)) \<in>
              borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
          unfolding slp_restrict_field_def
          using centers_measurable X_measurable abstract_iterate by measurable
      qed

      have fiber_bounds:
          "\<And>j c. AE z in lborel.
            Real_Vector_Spaces.norm (?U j c z) \<le>
              ?majorant c * ?rho ^ j"
      proof -
        fix j :: nat and c :: slp_point
        show
          "AE z in lborel.
            Real_Vector_Spaces.norm (?U j c z) \<le>
              ?majorant c * ?rho ^ j"
        proof (cases "c \<in> centers")
          case True
          have geometry:
              "\<forall>y. y \<in> X \<longrightarrow>
                Real_Vector_Spaces.norm (y - c) \<le> R"
            using center_geometry[OF True] by blast
          have at_center:
              "?rho \<le> 1 / 2 \<and>
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
                            (slp_partial_inverse coefficient c)) * ?rho ^ j)
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
                            (slp_partial_inverse coefficient c)) * ?rho ^ j)
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
                          (slp_partial_inverse coefficient c)) * ?rho ^ j)"
            using iterate_data[rule_format, of tau c] tau_large geometry by blast
          have bound:
              "AE z in lborel.
                Real_Vector_Spaces.norm
                  (slp_restrict_field X
                    (slp_neumann_iterate
                      (slp_right_neumann_step tau c cutoff coefficient)
                      (slp_right_neumann_base tau c cutoff coefficient
                        SLP_Partial_Inverse) j) z)
                \<le> C * tau powr (-(1 - 1 / p) + epsilon) *
                  (aim_complex_lp_norm p coefficient +
                    Real_Vector_Spaces.norm
                      (slp_partial_inverse coefficient c)) * ?rho ^ j"
            using at_center by blast
          show ?thesis
            using bound True by simp
        next
          case False
          then show ?thesis by simp
        qed
      qed
      have fiber_bounds_AE:
          "\<And>j. AE c in lborel. AE z in lborel.
            Real_Vector_Spaces.norm (?U j c z) \<le>
              ?majorant c * ?rho ^ j"
        by (rule AE_I2) (rule fiber_bounds)

      note joint = slp_joint_measurable_geometric_series_from_fibers[
        where U = ?U and majorant = ?majorant and rho = ?rho,
        OF term_measurable majorant_measurable majorant_nonnegative
          rho_nonnegative rho_strict fiber_bounds_AE]

      show
        "(let rho = CV * tau powr (-(1 - 1 / p) + epsilon);
              majorant = (\<lambda>c.
                if c \<in> centers
                then C * tau powr (-(1 - 1 / p) + epsilon) *
                  (aim_complex_lp_norm p coefficient +
                    Real_Vector_Spaces.norm (slp_partial_inverse coefficient c))
                else 0);
              U = (\<lambda>j c z.
                if c \<in> centers
                then slp_restrict_field X
                  (slp_neumann_iterate
                    (slp_right_neumann_step tau c cutoff coefficient)
                    (slp_right_neumann_base tau c cutoff coefficient
                      SLP_Partial_Inverse) j) z
                else 0)
          in rho \<le> 1 / 2
            \<and> (AE pair in lborel \<Otimes>\<^sub>M lborel. \<forall>j.
              Real_Vector_Spaces.norm
                (U j (fst pair) (snd pair)) \<le>
                majorant (fst pair) * rho ^ j)
            \<and> (\<lambda>pair :: slp_point \<times> slp_point.
              \<Sum>j. U j (fst pair) (snd pair)) \<in>
                borel_measurable (lborel \<Otimes>\<^sub>M lborel)
            \<and> (AE pair in lborel \<Otimes>\<^sub>M lborel.
              summable (\<lambda>j.
                Real_Vector_Spaces.norm (U j (fst pair) (snd pair))))
            \<and> (AE pair in lborel \<Otimes>\<^sub>M lborel.
              summable (\<lambda>j. U j (fst pair) (snd pair)))
            \<and> (AE pair in lborel \<Otimes>\<^sub>M lborel.
              Real_Vector_Spaces.norm
                (\<Sum>j. U j (fst pair) (snd pair)) \<le>
                majorant (fst pair) / (1 - rho)))"
        unfolding Let_def
        using rho_half joint(1) joint(2) joint(3) joint(4) joint(5)
        by blast
    qed
  qed
qed

end

end
