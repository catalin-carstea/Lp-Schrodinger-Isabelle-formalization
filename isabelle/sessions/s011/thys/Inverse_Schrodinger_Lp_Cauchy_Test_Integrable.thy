theory Inverse_Schrodinger_Lp_Cauchy_Test_Integrable
  imports
    Inverse_Schrodinger_Lp_Near_Center_Operator_Bridge
    Inverse_Schrodinger_Lp_Weak_Test_Multiplier
begin

section \<open>Every-point Cauchy integrability of test functions\<close>

theorem slp_test_function_cauchy_integrable_at:
  assumes f_test: "slp_test_function_on UNIV f"
  shows "slp_cauchy_integrable_at orientation f z"
proof -
  let ?K = "closure {x. f x \<noteq> 0}"
  have f_smooth: "smooth_on UNIV f"
    using f_test unfolding slp_test_function_on_def by blast
  have K_compact: "compact ?K"
    using f_test unfolding slp_test_function_on_def by blast
  have K_bounded: "bounded ?K"
    by (rule compact_imp_bounded[OF K_compact])
  then obtain A where A_bound:
      "\<And>x. x \<in> ?K \<Longrightarrow> norm x \<le> A"
    unfolding bounded_iff by blast
  let ?R = "norm z + max 0 A"
  have R_nonnegative: "0 \<le> ?R"
    by simp
  have support_distance:
      "\<And>y. y \<in> ?K \<Longrightarrow> norm (z - y) \<le> ?R"
  proof -
    fix y
    assume y_in: "y \<in> ?K"
    have "norm (z - y) \<le> norm z + norm y"
      by (rule norm_triangle_ineq4)
    also have "... \<le> norm z + max 0 A"
      using A_bound[OF y_in] by linarith
    finally show "norm (z - y) \<le> ?R" .
  qed

  have f_continuous: "continuous_on UNIV f"
    by (rule smooth_on_imp_continuous_on[OF f_smooth])
  have image_bounded: "bounded (f ` ?K)"
    by (rule compact_imp_bounded)
       (rule compact_continuous_image[OF
          continuous_on_subset[OF f_continuous subset_UNIV] K_compact])
  then obtain B where B_bound:
      "\<And>x. x \<in> ?K \<Longrightarrow> norm (f x) \<le> B"
    unfolding bounded_iff by blast
  let ?M = "max 0 B"
  have M_nonnegative: "0 \<le> ?M"
    by simp
  have f_bound: "\<And>x. x \<in> ?K \<Longrightarrow> norm (f x) \<le> ?M"
    using B_bound by fastforce

  have f_measurable: "f \<in> borel_measurable lborel"
    using borel_measurable_continuous_onI[OF f_continuous] by simp
  let ?majorant = "\<lambda>y.
    ?M * slp_localized_cauchy_kernel ?R (z - y)"
  have kernel_integrable:
      "integrable lborel
        (\<lambda>y. slp_localized_cauchy_kernel ?R (z - y))"
    by (rule slp_localized_cauchy_kernel_translate_integrable)
  have majorant_integrable: "integrable lborel ?majorant"
    using kernel_integrable by (rule integrable_mult_right)
  have norm_kernel_integrable:
      "integrable lborel
        (\<lambda>y. norm (f y) *
          norm (slp_cauchy_kernel orientation z y))"
  proof (rule Bochner_Integration.integrable_bound[OF majorant_integrable])
    show "(\<lambda>y. norm (f y) *
        norm (slp_cauchy_kernel orientation z y))
      \<in> borel_measurable lborel"
      using f_measurable slp_cauchy_kernel_borel_measurable by measurable
    show "AE y in lborel.
      norm (norm (f y) * norm (slp_cauchy_kernel orientation z y)) \<le>
        norm (?majorant y)"
    proof (rule AE_I2)
      fix y :: slp_point
      show "norm (norm (f y) *
          norm (slp_cauchy_kernel orientation z y)) \<le>
        norm (?majorant y)"
      proof (cases "f y = 0")
        case True
        then show ?thesis by simp
      next
        case False
        have y_in: "y \<in> ?K"
          by (rule subsetD[OF closure_subset]) (simp add: False)
        have distance: "norm (z - y) \<le> ?R"
          by (rule support_distance[OF y_in])
        have localized:
            "slp_localized_cauchy_kernel ?R (z - y) =
              inverse (norm (z - y))"
          by (rule slp_localized_cauchy_kernel_inside[OF distance])
        have kernel_nonnegative:
            "0 \<le> slp_localized_cauchy_kernel ?R (z - y)"
          by (rule slp_localized_cauchy_kernel_nonnegative)
        have product_bound:
            "norm (f y) * slp_localized_cauchy_kernel ?R (z - y) \<le>
              ?M * slp_localized_cauchy_kernel ?R (z - y)"
          by (rule mult_right_mono[OF f_bound[OF y_in]
                kernel_nonnegative])
        show ?thesis
          using M_nonnegative kernel_nonnegative product_bound
          by (simp only: slp_cauchy_kernel_norm slp_radial_inverse_def
              localized norm_mult real_norm_def abs_of_nonneg
              mult_nonneg_nonneg norm_ge_zero)
      qed
    qed
  qed
  show ?thesis
    by (rule slp_cauchy_integrable_at_of_norm_majorant[OF
          f_measurable norm_kernel_integrable])
qed

end
