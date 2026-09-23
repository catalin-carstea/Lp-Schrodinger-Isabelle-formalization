theory Inverse_Schrodinger_Lp_Dbar_Psi_Quarter_Turn_Covariance
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_010.Inverse_Schrodinger_Lp_Quarter_Turn_Transport"
begin

section \<open>Quarter-turn covariance of the oscillatory dbar-Cauchy operator\<close>

lemma slp_test_function_on_inverse_quarter_turn:
  assumes f_test: "slp_test_function_on UNIV f"
  shows "slp_test_function_on UNIV
    (\<lambda>x. f (- slp_quarter_turn x))"
proof -
  let ?K = "closure {x. f x \<noteq> 0}"
  have f_smooth: "smooth_on UNIV f"
    and K_compact: "compact ?K"
    using f_test unfolding slp_test_function_on_def by blast+
  have R_bounded_linear: "bounded_linear slp_quarter_turn"
    using slp_quarter_turn_linear
    by (simp only: linear_conv_bounded_linear)
  have R_smooth: "smooth_on UNIV slp_quarter_turn"
    by (rule bounded_linear.smooth_on[OF R_bounded_linear])
  have inverse_R_bounded_linear:
      "bounded_linear (\<lambda>x. - slp_quarter_turn x)"
    using bounded_linear_minus[OF R_bounded_linear]
    by simp
  have inverse_R_smooth:
      "smooth_on UNIV (\<lambda>x. - slp_quarter_turn x)"
    by (rule bounded_linear.smooth_on[OF inverse_R_bounded_linear])
  have pullback_smooth:
      "smooth_on UNIV (\<lambda>x. f (- slp_quarter_turn x))"
  proof -
    have "smooth_on UNIV (f \<circ> (\<lambda>x. - slp_quarter_turn x))"
      by (rule smooth_on_compose[OF f_smooth inverse_R_smooth]) auto
    then show ?thesis
      by (simp only: o_def)
  qed
  have image_compact: "compact (slp_quarter_turn ` ?K)"
    by (rule slp_quarter_turn_compact_image[OF K_compact])
  have nonzero_subset:
      "{x. f (- slp_quarter_turn x) \<noteq> 0} \<subseteq>
        slp_quarter_turn ` ?K"
  proof
    fix x
    assume x_nonzero: "x \<in> {x. f (- slp_quarter_turn x) \<noteq> 0}"
    have source_in: "- slp_quarter_turn x \<in> ?K"
      by (rule subsetD[OF closure_subset]) (use x_nonzero in simp)
    show "x \<in> slp_quarter_turn ` ?K"
      by (rule image_eqI[where x="- slp_quarter_turn x"])
        (use source_in in simp_all)
  qed
  have support_subset:
      "closure {x. f (- slp_quarter_turn x) \<noteq> 0} \<subseteq>
        slp_quarter_turn ` ?K"
    by (rule closure_minimal[OF nonzero_subset
          compact_imp_closed[OF image_compact]])
  have support_compact:
      "compact (closure {x. f (- slp_quarter_turn x) \<noteq> 0})"
    by (rule compact_if_closed_subset_of_compact[OF
          closed_closure image_compact support_subset])
  show ?thesis
    unfolding slp_test_function_on_def
    using pullback_smooth support_compact by simp
qed

lemma slp_dbar_cauchy_kernel_quarter_turn:
  "slp_cauchy_kernel SLP_Dbar_Inverse
      (slp_quarter_turn z) (slp_quarter_turn y) =
    - \<i> * slp_cauchy_kernel SLP_Dbar_Inverse z y"
proof -
  have point_difference:
      "slp_point_as_complex (slp_quarter_turn z) -
          slp_point_as_complex (slp_quarter_turn y) =
        \<i> * (slp_point_as_complex z - slp_point_as_complex y)"
    by (simp only: slp_quarter_turn_as_complex
          right_diff_distrib[symmetric])
  have denominator_rotation:
      "slp_cauchy_denominator SLP_Dbar_Inverse
          (slp_quarter_turn z) (slp_quarter_turn y) =
        \<i> * slp_cauchy_denominator SLP_Dbar_Inverse z y"
    unfolding slp_cauchy_denominator_def
    by (simp only: slp_cauchy_orientation.simps point_difference)
  show ?thesis
    unfolding slp_cauchy_kernel_def denominator_rotation
    by (simp only: inverse_mult_distrib inverse_i mult.commute)
qed

lemma slp_center_kernel_quarter_turn:
  "slp_center_kernel tau (slp_quarter_turn c) (slp_quarter_turn z) =
    slp_center_kernel (- tau) c z"
  unfolding slp_center_kernel_def
  by (simp add: algebra_simps)

theorem slp_dbar_psi_inverse_quarter_turn:
  assumes f_test: "slp_test_function_on UNIV f"
  shows
    "slp_dbar_psi_inverse tau (slp_quarter_turn c)
        (\<lambda>x. f (- slp_quarter_turn x)) (slp_quarter_turn z) =
      - \<i> * slp_dbar_psi_inverse (- tau) c f z"
proof -
  let ?g = "\<lambda>x. f (- slp_quarter_turn x)"
  let ?left_source =
    "slp_oscillatory_modulation (- tau) (slp_quarter_turn c) ?g"
  let ?right_source = "slp_oscillatory_modulation tau c f"
  let ?left_integrand =
    "slp_cauchy_integrand SLP_Dbar_Inverse ?left_source
      (slp_quarter_turn z)"
  let ?right_integrand =
    "slp_cauchy_integrand SLP_Dbar_Inverse ?right_source z"

  have g_test: "slp_test_function_on UNIV ?g"
    by (rule slp_test_function_on_inverse_quarter_turn[OF f_test])
  have g_smooth: "smooth_on UNIV ?g"
    using g_test unfolding slp_test_function_on_def by blast
  have g_measurable: "?g \<in> borel_measurable lborel"
    using borel_measurable_continuous_onI[
        OF smooth_on_imp_continuous_on[OF g_smooth]]
    by simp
  have left_source_measurable:
      "?left_source \<in> borel_measurable lborel"
    by (rule slp_oscillatory_modulation_measurable[OF g_measurable])
  have left_integrand_measurable:
      "?left_integrand \<in> borel_measurable lborel"
    by (rule slp_cauchy_integrand_borel_measurable[
          OF left_source_measurable])
  have left_integrand_borel:
      "?left_integrand \<in>
        borel_measurable (borel :: slp_point measure)"
    using left_integrand_measurable
    by (simp only: measurable_lborel2)
  have R_lborel_measurable:
      "slp_quarter_turn \<in>
        measurable (lborel :: slp_point measure) borel"
    using slp_quarter_turn_measurable
    by (simp only: measurable_cong_sets[OF sets_lborel refl])
  have transported_integral:
      "integral\<^sup>L lborel ?left_integrand =
        integral\<^sup>L lborel (\<lambda>y. ?left_integrand (slp_quarter_turn y))"
  proof -
    have raw:
        "integral\<^sup>L
            (distr (lborel :: slp_point measure) borel slp_quarter_turn)
              ?left_integrand =
          integral\<^sup>L lborel
            (\<lambda>y. ?left_integrand (slp_quarter_turn y))"
      by (rule integral_distr[OF R_lborel_measurable
            left_integrand_borel])
    show ?thesis
      using raw by (simp only: slp_quarter_turn_distr_lborel)
  qed
  have rotated_integrand:
      "(\<lambda>y. ?left_integrand (slp_quarter_turn y)) =
        (\<lambda>y. - \<i> * ?right_integrand y)"
  proof (rule ext)
    fix y :: slp_point
    show "?left_integrand (slp_quarter_turn y) =
        - \<i> * ?right_integrand y"
      unfolding slp_cauchy_integrand_def
        slp_oscillatory_modulation_def
      by (simp add: slp_center_kernel_quarter_turn
          slp_dbar_cauchy_kernel_quarter_turn algebra_simps)
  qed
  have right_source_test: "slp_test_function_on UNIV ?right_source"
    unfolding slp_oscillatory_modulation_def
    by (rule slp_test_function_on_mult_left[
          OF slp_center_kernel_smooth f_test])
  have right_integrable_at:
      "slp_cauchy_integrable_at SLP_Dbar_Inverse ?right_source z"
    by (rule slp_test_function_cauchy_integrable_at[OF
          right_source_test])
  have right_integrable: "integrable lborel ?right_integrand"
    using right_integrable_at
    unfolding slp_cauchy_integrable_at_def .
  have scalar_integral:
      "integral\<^sup>L lborel (\<lambda>y. - \<i> * ?right_integrand y) =
        - \<i> * integral\<^sup>L lborel ?right_integrand"
    by (rule Bochner_Integration.integral_mult_right[OF
          right_integrable])
  have integral_covariance:
      "integral\<^sup>L lborel ?left_integrand =
        - \<i> * integral\<^sup>L lborel ?right_integrand"
    using transported_integral
    by (simp only: rotated_integrand scalar_integral)
  show ?thesis
    unfolding slp_dbar_psi_inverse_eq slp_cauchy_transform_def
    using integral_covariance
    by (simp add: algebra_simps)
qed

end
