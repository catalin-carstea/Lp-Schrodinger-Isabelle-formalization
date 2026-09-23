theory Inverse_Schrodinger_Lp_Born_One_Sided_Smooth_Error_Limits
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Born_One_Sided_Center_Average_Pairing_Limits"
begin

section \<open>One-sided smooth center-average error limits\<close>

lemma slp_test_function_integrable_bounded:
  assumes phi_test: "slp_test_function_on UNIV phi"
  shows "integrable lborel phi" and "bounded (range phi)"
proof -
  let ?K = "closure {x. phi x \<noteq> 0}"
  have phi_smooth: "smooth_on UNIV phi"
    using phi_test unfolding slp_test_function_on_def by blast
  have K_compact: "compact ?K"
    using phi_test unfolding slp_test_function_on_def by blast
  have phi_continuous: "continuous_on UNIV phi"
    by (rule smooth_on_imp_continuous_on[OF phi_smooth])
  have phi_continuous_K: "continuous_on ?K phi"
    by (rule continuous_on_subset[OF phi_continuous]) simp
  obtain B where B_nonnegative: "0 \<le> B"
    and phi_bound_K:
      "\<And>x. x \<in> ?K \<Longrightarrow> Real_Vector_Spaces.norm (phi x) \<le> B"
    using continuous_on_compact_bound[OF K_compact phi_continuous_K]
    by blast
  have phi_zero_outside: "\<And>x. x \<notin> ?K \<Longrightarrow> phi x = 0"
    by auto
  have phi_measurable: "phi \<in> borel_measurable lborel"
    using borel_measurable_continuous_onI[OF phi_continuous] by simp
  show "integrable lborel phi"
  proof (rule Bochner_Integration.integrableI_bounded_set[
      where A="?K" and B=B])
    show "?K \<in> sets lborel"
      using borel_compact[OF K_compact] by simp
    show "phi \<in> borel_measurable lborel"
      by (rule phi_measurable)
    show "emeasure lborel ?K < \<infinity>"
      by (rule emeasure_compact_finite[OF K_compact])
    show "AE x in lborel. x \<in> ?K \<longrightarrow>
        Real_Vector_Spaces.norm (phi x) \<le> B"
      by (intro always_eventually allI impI phi_bound_K)
    show "AE x in lborel. x \<notin> ?K \<longrightarrow> phi x = 0"
      by (intro always_eventually allI impI phi_zero_outside)
  qed
  have range_subset: "range phi \<subseteq> insert 0 (phi ` ?K)"
  proof
    fix y
    assume "y \<in> range phi"
    then obtain x where y: "y = phi x" by blast
    show "y \<in> insert 0 (phi ` ?K)"
    proof (cases "x \<in> ?K")
      case True
      then show ?thesis using y by blast
    next
      case False
      then have "phi x = 0" by (rule phi_zero_outside)
      then show ?thesis using y by simp
    qed
  qed
  have "compact (insert 0 (phi ` ?K))"
    by (intro compact_insert compact_continuous_image
          phi_continuous_K K_compact)
  then have "bounded (insert 0 (phi ` ?K))"
    by (rule compact_imp_bounded)
  then show "bounded (range phi)"
    by (rule bounded_subset[OF _ range_subset])
qed

lemma slp_center_average_test_error_pairing_convergence:
  fixes F phi :: "slp_point \<Rightarrow> complex"
  assumes F_integrable: "integrable lborel F"
    and phi_test: "slp_test_function_on UNIV phi"
    and uniform_convergence:
      "uniform_limit UNIV
        (\<lambda>tau. slp_center_average tau phi) phi at_top"
  shows
    "((\<lambda>tau. integral\<^sup>L lborel (\<lambda>c.
        F c * (slp_center_average tau phi c - phi c)))
      \<longlongrightarrow> 0) at_top"
proof -
  have phi_integrable: "integrable lborel phi"
    by (rule slp_test_function_integrable_bounded(1)[OF phi_test])
  have phi_bounded: "bounded (range phi)"
    by (rule slp_test_function_integrable_bounded(2)[OF phi_test])
  have pairing_limit:
      "((\<lambda>tau. integral\<^sup>L lborel (\<lambda>c.
          F c * slp_center_average tau phi c))
        \<longlongrightarrow>
          integral\<^sup>L lborel (\<lambda>c. F c * phi c)) at_top"
    by (rule slp_center_average_pairing_convergence[OF
          F_integrable phi_integrable phi_bounded uniform_convergence])
  have difference_limit:
      "((\<lambda>tau. integral\<^sup>L lborel (\<lambda>c.
          F c * slp_center_average tau phi c) -
        integral\<^sup>L lborel (\<lambda>c. F c * phi c))
        \<longlongrightarrow> 0) at_top"
  proof -
    have constant_limit:
        "((\<lambda>_ :: real. integral\<^sup>L lborel (\<lambda>c. F c * phi c))
          \<longlongrightarrow> integral\<^sup>L lborel (\<lambda>c. F c * phi c))
          at_top"
      by (rule tendsto_const)
    show ?thesis
      using tendsto_diff[OF pairing_limit constant_limit] by simp
  qed
  have phi_measurable: "phi \<in> borel_measurable lborel"
    using phi_integrable by measurable
  obtain B where phi_bound:
      "\<And>c. Real_Vector_Spaces.norm (phi c) \<le> B"
    using phi_bounded unfolding bounded_iff by auto
  have B_nonnegative: "0 \<le> B"
    using norm_ge_zero[of "phi 0"] phi_bound[of 0] by linarith
  have limiting_pair_integrable:
      "integrable lborel (\<lambda>c. F c * phi c)"
    by (rule slp_integrable_bilinear_mult_bounded[OF
          F_integrable phi_measurable B_nonnegative phi_bound])
  have error_integral_eq:
      "integral\<^sup>L lborel (\<lambda>c.
          F c * (slp_center_average tau phi c - phi c)) =
        integral\<^sup>L lborel (\<lambda>c.
          F c * slp_center_average tau phi c) -
        integral\<^sup>L lborel (\<lambda>c. F c * phi c)" for tau
  proof -
    let ?Btau =
      "Real_Vector_Spaces.norm (of_real (tau / pi) :: complex) *
        integral\<^sup>L lborel (\<lambda>z. Real_Vector_Spaces.norm (phi z))"
    have Btau_nonnegative: "0 \<le> ?Btau"
      by (intro mult_nonneg_nonneg) simp_all
    have average_bound:
        "Real_Vector_Spaces.norm (slp_center_average tau phi c) \<le> ?Btau"
      for c
      by (rule slp_center_average_fixed_tau_bound)
    have averaged_pair_integrable:
        "integrable lborel
          (\<lambda>c. F c * slp_center_average tau phi c)"
      by (rule slp_integrable_bilinear_mult_bounded[OF
          F_integrable slp_center_average_measurable[OF phi_integrable]
          Btau_nonnegative average_bound])
    have "integral\<^sup>L lborel (\<lambda>c.
          F c * (slp_center_average tau phi c - phi c)) =
        integral\<^sup>L lborel (\<lambda>c.
          F c * slp_center_average tau phi c - F c * phi c)"
      by (rule Bochner_Integration.integral_cong[OF refl])
        (simp add: algebra_simps)
    also have "... =
        integral\<^sup>L lborel (\<lambda>c.
          F c * slp_center_average tau phi c) -
        integral\<^sup>L lborel (\<lambda>c. F c * phi c)"
      by (rule Bochner_Integration.integral_diff[OF
            averaged_pair_integrable limiting_pair_integrable])
    finally show ?thesis .
  qed
  have function_eq:
      "(\<lambda>tau. integral\<^sup>L lborel (\<lambda>c.
          F c * (slp_center_average tau phi c - phi c))) =
        (\<lambda>tau. integral\<^sup>L lborel (\<lambda>c.
          F c * slp_center_average tau phi c) -
        integral\<^sup>L lborel (\<lambda>c. F c * phi c))"
    by (rule ext) (rule error_integral_eq)
  show ?thesis
    using difference_limit unfolding function_eq .
qed

context aim_planar_riesz_hls
begin

theorem slp_left_right_one_sided_smooth_error_limits:
  fixes R C p :: real
    and X :: "slp_point set"
    and cutoff potential phi :: "slp_point \<Rightarrow> complex"
  assumes radius_nonnegative: "0 \<le> R"
    and p_lower: "1 < p"
    and p_upper: "p < 2"
    and X_measurable: "X \<in> sets lborel"
    and X_bounded: "bounded X"
    and cutoff_measurable: "cutoff \<in> borel_measurable lborel"
    and potential_lp: "aim_complex_lp_on_plane p potential"
    and potential_outside: "\<And>x. x \<notin> X \<Longrightarrow> potential x = 0"
    and cutoff_bound: "\<And>x. cmod (cutoff x) \<le> C"
    and C_nonnegative: "0 \<le> C"
    and phi_test: "slp_test_function_on UNIV phi"
    and phi_uniform_convergence:
      "uniform_limit UNIV
        (\<lambda>tau. slp_center_average tau phi) phi at_top"
  shows left_limit:
      "((\<lambda>tau. integral\<^sup>L lborel (\<lambda>output.
          of_real (enn2real
            (slp_left_one_sided_output_density R cutoff potential
              (\<lambda>_. 1) n potential output)) *
          (slp_center_average tau phi output - phi output)))
        \<longlongrightarrow> 0) at_top"
    and right_limit:
      "((\<lambda>tau. integral\<^sup>L lborel (\<lambda>output.
          of_real (enn2real
            (slp_right_one_sided_output_density R cutoff potential
              (\<lambda>_. 1) n potential output)) *
          (slp_center_average tau phi output - phi output)))
        \<longlongrightarrow> 0) at_top"
proof -
  have left_real_integrable:
      "integrable lborel (\<lambda>output. enn2real
        (slp_left_one_sided_output_density R cutoff potential
          (\<lambda>_. 1) n potential output))"
    by (rule slp_left_right_one_sided_output_density_real_all_orders_l1(1)[OF
          radius_nonnegative p_lower p_upper X_measurable X_bounded
          cutoff_measurable potential_lp potential_outside cutoff_bound
          C_nonnegative])
  have right_real_integrable:
      "integrable lborel (\<lambda>output. enn2real
        (slp_right_one_sided_output_density R cutoff potential
          (\<lambda>_. 1) n potential output))"
    by (rule slp_left_right_one_sided_output_density_real_all_orders_l1(2)[OF
          radius_nonnegative p_lower p_upper X_measurable X_bounded
          cutoff_measurable potential_lp potential_outside cutoff_bound
          C_nonnegative])
  have left_complex_integrable:
      "integrable lborel (\<lambda>output. of_real (enn2real
        (slp_left_one_sided_output_density R cutoff potential
          (\<lambda>_. 1) n potential output)))"
    using left_real_integrable by simp
  have right_complex_integrable:
      "integrable lborel (\<lambda>output. of_real (enn2real
        (slp_right_one_sided_output_density R cutoff potential
          (\<lambda>_. 1) n potential output)))"
    using right_real_integrable by simp
  show left_limit:
      "((\<lambda>tau. integral\<^sup>L lborel (\<lambda>output.
          of_real (enn2real
            (slp_left_one_sided_output_density R cutoff potential
              (\<lambda>_. 1) n potential output)) *
          (slp_center_average tau phi output - phi output)))
        \<longlongrightarrow> 0) at_top"
    by (rule slp_center_average_test_error_pairing_convergence[OF
          left_complex_integrable phi_test phi_uniform_convergence])
  show right_limit:
      "((\<lambda>tau. integral\<^sup>L lborel (\<lambda>output.
          of_real (enn2real
            (slp_right_one_sided_output_density R cutoff potential
              (\<lambda>_. 1) n potential output)) *
          (slp_center_average tau phi output - phi output)))
        \<longlongrightarrow> 0) at_top"
    by (rule slp_center_average_test_error_pairing_convergence[OF
          right_complex_integrable phi_test phi_uniform_convergence])
qed

end

end
