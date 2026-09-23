theory Inverse_Schrodinger_Lp_Center_Average_Pairing
  imports Inverse_Schrodinger_Lp_Center_Average_Physical
begin

section \<open>Conditional convergence of center-average pairings\<close>

lemma slp_center_average_measurable:
  fixes phi :: "slp_point \<Rightarrow> complex"
  assumes phi_integrable: "integrable lborel phi"
  shows "slp_center_average tau phi \<in> borel_measurable lborel"
proof -
  have phi_measurable[measurable]:
    "phi \<in> borel_measurable (lborel :: slp_point measure)"
    using phi_integrable by measurable
  have phi_snd_measurable[measurable]:
    "(\<lambda>p :: slp_point \<times> slp_point. phi (snd p)) \<in>
      borel_measurable
        ((lborel :: slp_point measure) \<Otimes>\<^sub>M
          (lborel :: slp_point measure))"
    using measurable_snd''[
      OF phi_measurable,
      where P="lborel :: slp_point measure"] .
  have phase_continuous:
    "continuous_on UNIV
      (\<lambda>p :: slp_point \<times> slp_point.
        slp_center_phase (fst p) (snd p))"
    unfolding slp_center_phase_def
    by (intro continuous_intros)
  have phase_raw:
    "(\<lambda>p :: slp_point \<times> slp_point.
        slp_center_phase (fst p) (snd p)) \<in>
      borel_measurable
        (lborel :: (slp_point \<times> slp_point) measure)"
    using borel_measurable_continuous_onI[OF phase_continuous]
    by simp
  have phase_measurable[measurable]:
    "(\<lambda>p :: slp_point \<times> slp_point.
        slp_center_phase (fst p) (snd p)) \<in>
      borel_measurable
        ((lborel :: slp_point measure) \<Otimes>\<^sub>M
          (lborel :: slp_point measure))"
    using phase_raw by (simp only: lborel_prod)
  have joint_integrand_measurable:
    "(\<lambda>p :: slp_point \<times> slp_point.
        slp_center_kernel tau (fst p) (snd p) * phi (snd p)) \<in>
      borel_measurable
        ((lborel :: slp_point measure) \<Otimes>\<^sub>M
          (lborel :: slp_point measure))"
    unfolding slp_center_kernel_def
    by measurable
  have parameter_integral_measurable:
    "(\<lambda>c. integral\<^sup>L lborel
        (\<lambda>z. slp_center_kernel tau c z * phi z)) \<in>
      borel_measurable (lborel :: slp_point measure)"
    by (rule lborel.borel_measurable_lebesgue_integral[
        where f="\<lambda>c z. slp_center_kernel tau c z * phi z"])
      (use joint_integrand_measurable in simp)
  show ?thesis
    unfolding slp_center_average_def
    using parameter_integral_measurable by measurable
qed

lemma slp_integrable_bilinear_mult_bounded:
  fixes F g :: "slp_point \<Rightarrow> complex"
  assumes F_integrable: "integrable lborel F"
    and g_measurable: "g \<in> borel_measurable lborel"
    and B_nonnegative: "0 \<le> B"
    and g_bound: "\<And>c. norm (g c) \<le> B"
  shows "integrable lborel (\<lambda>c. F c * g c)"
proof (rule Bochner_Integration.integrable_bound[
    of lborel "\<lambda>c. of_real B * F c"])
  show "integrable lborel (\<lambda>c. of_real B * F c)"
    using F_integrable by simp
  show "(\<lambda>c. F c * g c) \<in> borel_measurable lborel"
    using F_integrable g_measurable by measurable
  show "AE c in lborel.
      norm (F c * g c) \<le> norm (of_real B * F c)"
  proof (intro always_eventually allI)
    fix c
    have "norm (F c) * norm (g c) \<le> norm (F c) * B"
      by (rule mult_left_mono[OF g_bound norm_ge_zero])
    then show "norm (F c * g c) \<le> norm (of_real B * F c)"
      using B_nonnegative
      by (simp only: norm_mult norm_of_real abs_of_nonneg)
        (simp add: mult.commute)
  qed
qed

theorem slp_center_average_pairing_convergence:
  fixes F phi :: "slp_point \<Rightarrow> complex"
  assumes F_integrable: "integrable lborel F"
    and phi_integrable: "integrable lborel phi"
    and phi_bounded: "bounded (range phi)"
    and uniform_convergence:
      "uniform_limit UNIV
        (\<lambda>tau. slp_center_average tau phi) phi at_top"
  shows
    "((\<lambda>tau. integral\<^sup>L lborel
        (\<lambda>c. F c * slp_center_average tau phi c))
      \<longlongrightarrow>
        integral\<^sup>L lborel (\<lambda>c. F c * phi c)) at_top"
proof (unfold tendsto_iff, intro allI impI)
  obtain B where phi_bound: "\<And>c. norm (phi c) \<le> B"
    using phi_bounded unfolding bounded_iff by auto
  have B_nonnegative: "0 \<le> B"
    using norm_ge_zero[of "phi 0"] phi_bound[of 0] by linarith
  have phi_measurable: "phi \<in> borel_measurable lborel"
    using phi_integrable by measurable
  have limiting_pair_integrable:
    "integrable lborel (\<lambda>c. F c * phi c)"
    by (rule slp_integrable_bilinear_mult_bounded[
        OF F_integrable phi_measurable B_nonnegative phi_bound])
  fix epsilon :: real
  assume epsilon_positive: "0 < epsilon"
  let ?L = "integral\<^sup>L lborel (\<lambda>c. norm (F c))"
  let ?delta = "epsilon / (?L + 1)"
  have L_nonnegative: "0 \<le> ?L"
    by (rule Bochner_Integration.integral_nonneg) simp
  have denominator_positive: "0 < ?L + 1"
    using L_nonnegative by linarith
  have delta_positive: "0 < ?delta"
    using epsilon_positive denominator_positive by (rule divide_pos_pos)
  have delta_times_denominator: "?delta * (?L + 1) = epsilon"
    using denominator_positive by simp
  have delta_times_L_less: "?delta * ?L < epsilon"
  proof -
    have "?delta * ?L < ?delta * (?L + 1)"
      using delta_positive by (intro mult_strict_left_mono) simp
    then show ?thesis
      by (simp only: delta_times_denominator)
  qed
  have uniform_event:
    "\<forall>\<^sub>F tau in at_top. \<forall>c\<in>UNIV.
      dist (slp_center_average tau phi c) (phi c) < ?delta"
    using uniform_limitD[OF uniform_convergence delta_positive] .
  show "\<forall>\<^sub>F tau in at_top.
      dist
        (integral\<^sup>L lborel
          (\<lambda>c. F c * slp_center_average tau phi c))
        (integral\<^sup>L lborel (\<lambda>c. F c * phi c)) < epsilon"
    using uniform_event
  proof eventually_elim
    fix tau
    assume tau_uniform:
      "\<forall>c\<in>UNIV.
        dist (slp_center_average tau phi c) (phi c) < ?delta"
    have difference_measurable:
      "(\<lambda>c. slp_center_average tau phi c - phi c) \<in>
        borel_measurable lborel"
      using slp_center_average_measurable[OF phi_integrable]
        phi_measurable
      by measurable
    have difference_bound:
      "norm (slp_center_average tau phi c - phi c) \<le> ?delta" for c
    proof -
      have "norm (slp_center_average tau phi c - phi c) < ?delta"
        using tau_uniform[rule_format, of c]
        by (simp add: dist_norm)
      then show ?thesis by (rule less_imp_le)
    qed
    have error_integrable:
      "integrable lborel
        (\<lambda>c. F c * (slp_center_average tau phi c - phi c))"
      by (rule slp_integrable_bilinear_mult_bounded[
          OF F_integrable difference_measurable
            delta_positive[THEN less_imp_le] difference_bound])
    have averaged_pair_integrable:
      "integrable lborel
        (\<lambda>c. F c * slp_center_average tau phi c)"
    proof -
      let ?Btau =
        "norm (of_real (tau / pi) :: complex) *
          integral\<^sup>L lborel (\<lambda>z. norm (phi z))"
      have Btau_nonnegative: "0 \<le> ?Btau"
      proof (rule mult_nonneg_nonneg)
        show "0 \<le> norm (of_real (tau / pi) :: complex)"
          by simp
        show "0 \<le> integral\<^sup>L lborel (\<lambda>z. norm (phi z))"
          by (rule Bochner_Integration.integral_nonneg) simp
      qed
      have average_bound:
        "norm (slp_center_average tau phi c) \<le> ?Btau" for c
        by (rule slp_center_average_fixed_tau_bound)
      show ?thesis
        by (rule slp_integrable_bilinear_mult_bounded[
            where B="?Btau",
            OF F_integrable
              slp_center_average_measurable[OF phi_integrable]
              Btau_nonnegative average_bound])
    qed
    have integral_difference:
      "integral\<^sup>L lborel
          (\<lambda>c. F c * slp_center_average tau phi c) -
        integral\<^sup>L lborel (\<lambda>c. F c * phi c) =
        integral\<^sup>L lborel
          (\<lambda>c. F c * (slp_center_average tau phi c - phi c))"
    proof -
      have "integral\<^sup>L lborel
            (\<lambda>c. F c * slp_center_average tau phi c) -
          integral\<^sup>L lborel (\<lambda>c. F c * phi c) =
          integral\<^sup>L lborel
            (\<lambda>c. F c * slp_center_average tau phi c -
              F c * phi c)"
        using Bochner_Integration.integral_diff[
          OF averaged_pair_integrable limiting_pair_integrable]
        by simp
      also have "... = integral\<^sup>L lborel
          (\<lambda>c. F c *
            (slp_center_average tau phi c - phi c))"
        by (rule Bochner_Integration.integral_cong[OF refl])
          (simp add: algebra_simps)
      finally show ?thesis .
    qed
    have error_norm_integrable:
      "integrable lborel
        (\<lambda>c. norm
          (F c * (slp_center_average tau phi c - phi c)))"
      using error_integrable by simp
    have scaled_norm_integrable:
      "integrable lborel (\<lambda>c. ?delta * norm (F c))"
      using F_integrable by simp
    have pointwise_error_bound:
      "norm (F c * (slp_center_average tau phi c - phi c)) \<le>
        ?delta * norm (F c)" for c
    proof -
      have "norm (F c) *
          norm (slp_center_average tau phi c - phi c) \<le>
        norm (F c) * ?delta"
        by (rule mult_left_mono[OF difference_bound norm_ge_zero])
      then show ?thesis
        by (simp only: norm_mult mult.commute)
    qed
    have norm_error_le:
      "norm (integral\<^sup>L lborel
          (\<lambda>c. F c *
            (slp_center_average tau phi c - phi c))) \<le>
        ?delta * ?L"
    proof -
      have "norm (integral\<^sup>L lborel
          (\<lambda>c. F c *
            (slp_center_average tau phi c - phi c))) \<le>
        integral\<^sup>L lborel
          (\<lambda>c. norm
            (F c * (slp_center_average tau phi c - phi c)))"
        by (rule Bochner_Integration.integral_norm_bound)
      also have "... \<le>
          integral\<^sup>L lborel (\<lambda>c. ?delta * norm (F c))"
        by (rule Bochner_Integration.integral_mono[
            OF error_norm_integrable scaled_norm_integrable])
          (use pointwise_error_bound in simp)
      also have "... = ?delta * ?L"
        by simp
      finally show ?thesis .
    qed
    show "dist
        (integral\<^sup>L lborel
          (\<lambda>c. F c * slp_center_average tau phi c))
        (integral\<^sup>L lborel (\<lambda>c. F c * phi c)) < epsilon"
      using norm_error_le delta_times_L_less
      by (simp only: dist_norm integral_difference)
  qed
qed

end
