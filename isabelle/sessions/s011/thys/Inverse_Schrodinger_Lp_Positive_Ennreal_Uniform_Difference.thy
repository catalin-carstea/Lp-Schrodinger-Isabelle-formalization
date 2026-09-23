theory Inverse_Schrodinger_Lp_Positive_Ennreal_Uniform_Difference
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof.Inverse_Schrodinger_Lp_Center_Average_Pairing"
begin

section \<open>Uniform-difference convergence against positive L1 weights\<close>

lemma slp_nonnegative_integrable_uniform_difference_nn_integral_tendsto_zero:
  fixes F :: "slp_point \<Rightarrow> real"
    and g :: "real \<Rightarrow> slp_point \<Rightarrow> complex"
    and h :: "slp_point \<Rightarrow> complex"
  assumes F_integrable: "integrable lborel F"
    and F_nonnegative: "\<And>x. 0 \<le> F x"
    and g_measurable: "\<And>tau. g tau \<in> borel_measurable lborel"
    and h_measurable: "h \<in> borel_measurable lborel"
    and uniform_convergence: "uniform_limit UNIV g h at_top"
  shows
    "((\<lambda>tau. \<integral>\<^sup>+ x.
        ennreal (F x * norm (g tau x - h x)) \<partial>lborel)
      \<longlongrightarrow> 0) at_top"
proof -
  let ?L = "integral\<^sup>L lborel F"
  have L_nonnegative: "0 \<le> ?L"
    by (rule Bochner_Integration.integral_nonneg) (simp add: F_nonnegative)
  have real_integral_limit:
      "((\<lambda>tau. integral\<^sup>L lborel
          (\<lambda>x. F x * norm (g tau x - h x)))
        \<longlongrightarrow> 0) at_top"
  proof (unfold tendsto_iff, intro allI impI)
    fix epsilon :: real
    assume epsilon_positive: "0 < epsilon"
    let ?delta = "epsilon / (?L + 1)"
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
        "\<forall>\<^sub>F tau in at_top. \<forall>x\<in>UNIV.
          dist (g tau x) (h x) < ?delta"
      by (rule uniform_limitD[OF uniform_convergence delta_positive])
    show "\<forall>\<^sub>F tau in at_top.
        dist (integral\<^sup>L lborel
          (\<lambda>x. F x * norm (g tau x - h x))) 0 < epsilon"
      using uniform_event
    proof eventually_elim
      fix tau
      assume tau_uniform:
        "\<forall>x\<in>UNIV. dist (g tau x) (h x) < ?delta"
      have difference_measurable:
          "(\<lambda>x. g tau x - h x) \<in> borel_measurable lborel"
        using g_measurable[of tau] h_measurable by measurable
      have product_measurable:
          "(\<lambda>x. F x * norm (g tau x - h x)) \<in>
            borel_measurable lborel"
        using F_integrable difference_measurable by measurable
      have difference_bound: "norm (g tau x - h x) \<le> ?delta" for x
        using tau_uniform[rule_format, of x]
        by (simp add: dist_norm less_imp_le)
      have scaled_integrable: "integrable lborel (\<lambda>x. ?delta * F x)"
        using F_integrable by simp
      have product_integrable:
          "integrable lborel (\<lambda>x. F x * norm (g tau x - h x))"
      proof (rule Bochner_Integration.integrable_bound[OF
            scaled_integrable product_measurable])
        show "AE x in lborel.
            norm (F x * norm (g tau x - h x)) \<le>
              norm (?delta * F x)"
        proof (intro always_eventually allI)
          fix x :: slp_point
          have "F x * norm (g tau x - h x) \<le> F x * ?delta"
            by (rule mult_left_mono[OF difference_bound F_nonnegative])
          moreover have "0 \<le> F x * norm (g tau x - h x)"
            by (rule mult_nonneg_nonneg[OF F_nonnegative norm_ge_zero])
          moreover have "0 \<le> ?delta * F x"
            by (rule mult_nonneg_nonneg[OF
                  less_imp_le[OF delta_positive] F_nonnegative])
          ultimately show
            "norm (F x * norm (g tau x - h x)) \<le>
              norm (?delta * F x)"
            by (simp only: real_norm_def abs_of_nonneg mult.commute)
        qed
      qed
      have product_nonnegative:
          "0 \<le> F x * norm (g tau x - h x)" for x
        by (rule mult_nonneg_nonneg[OF F_nonnegative norm_ge_zero])
      have integral_nonnegative:
          "0 \<le> integral\<^sup>L lborel
            (\<lambda>x. F x * norm (g tau x - h x))"
        by (rule Bochner_Integration.integral_nonneg)
          (simp add: product_nonnegative)
      have pointwise_scaled:
          "F x * norm (g tau x - h x) \<le> ?delta * F x" for x
      proof -
        have "F x * norm (g tau x - h x) \<le> F x * ?delta"
          by (rule mult_left_mono[OF difference_bound F_nonnegative])
        then show ?thesis by (simp only: mult.commute)
      qed
      have integral_bound:
          "integral\<^sup>L lborel
              (\<lambda>x. F x * norm (g tau x - h x)) \<le>
            ?delta * ?L"
      proof -
        have "integral\<^sup>L lborel
              (\<lambda>x. F x * norm (g tau x - h x)) \<le>
            integral\<^sup>L lborel (\<lambda>x. ?delta * F x)"
        proof (rule Bochner_Integration.integral_mono[OF
              product_integrable scaled_integrable])
          fix x :: slp_point
          assume "x \<in> space lborel"
          show "F x * norm (g tau x - h x) \<le> ?delta * F x"
            by (rule pointwise_scaled)
        qed
        also have "... = ?delta * ?L"
          using F_integrable by simp
        finally show ?thesis .
      qed
      show "dist (integral\<^sup>L lborel
          (\<lambda>x. F x * norm (g tau x - h x))) 0 < epsilon"
        using integral_nonnegative integral_bound delta_times_L_less
        by (simp add: dist_real_def abs_of_nonneg)
    qed
  qed
  have eventual_product_integrable:
      "\<forall>\<^sub>F tau in at_top.
        integrable lborel (\<lambda>x. F x * norm (g tau x - h x))"
  proof -
    have uniform_event:
        "\<forall>\<^sub>F tau in at_top. \<forall>x\<in>UNIV.
          dist (g tau x) (h x) < 1"
      by (rule uniform_limitD[OF uniform_convergence zero_less_one])
    show ?thesis
      using uniform_event
    proof eventually_elim
      fix tau
      assume tau_uniform: "\<forall>x\<in>UNIV. dist (g tau x) (h x) < 1"
      have difference_measurable:
          "(\<lambda>x. g tau x - h x) \<in> borel_measurable lborel"
        using g_measurable[of tau] h_measurable by measurable
      show "integrable lborel (\<lambda>x. F x * norm (g tau x - h x))"
      proof (rule Bochner_Integration.integrable_bound[OF F_integrable])
        show "(\<lambda>x. F x * norm (g tau x - h x)) \<in>
            borel_measurable lborel"
          using F_integrable difference_measurable by measurable
        show "AE x in lborel.
            norm (F x * norm (g tau x - h x)) \<le> norm (F x)"
        proof (intro always_eventually allI)
          fix x :: slp_point
          have difference_bound: "norm (g tau x - h x) \<le> 1"
            using tau_uniform[rule_format, of x]
            by (simp add: dist_norm less_imp_le)
          have "F x * norm (g tau x - h x) \<le> F x * 1"
            by (rule mult_left_mono[OF difference_bound F_nonnegative])
          then show
            "norm (F x * norm (g tau x - h x)) \<le> norm (F x)"
            using F_nonnegative[of x]
            by (simp add: abs_of_nonneg)
        qed
      qed
    qed
  qed
  have ennreal_integral_limit:
      "((\<lambda>tau. ennreal (integral\<^sup>L lborel
          (\<lambda>x. F x * norm (g tau x - h x))))
        \<longlongrightarrow> 0) at_top"
    using tendsto_ennrealI[OF real_integral_limit] by simp
  show ?thesis
  proof (rule Lim_transform_eventually[OF ennreal_integral_limit])
    show "\<forall>\<^sub>F tau in at_top.
        ennreal (integral\<^sup>L lborel
          (\<lambda>x. F x * norm (g tau x - h x))) =
        (\<integral>\<^sup>+ x. ennreal
          (F x * norm (g tau x - h x)) \<partial>lborel)"
      using eventual_product_integrable
    proof eventually_elim
      fix tau
      assume product_integrable:
        "integrable lborel (\<lambda>x. F x * norm (g tau x - h x))"
      have equality:
          "(\<integral>\<^sup>+ x. F x * norm (g tau x - h x) \<partial>lborel) =
            integral\<^sup>L lborel
              (\<lambda>x. F x * norm (g tau x - h x))"
        by (rule Bochner_Integration.nn_integral_eq_integral[OF
              product_integrable])
          (simp add: F_nonnegative)
      show "ennreal (integral\<^sup>L lborel
          (\<lambda>x. F x * norm (g tau x - h x))) =
        (\<integral>\<^sup>+ x. ennreal
          (F x * norm (g tau x - h x)) \<partial>lborel)"
        using equality by simp
    qed
  qed
qed

lemma slp_positive_ennreal_uniform_difference_nn_integral_tendsto_zero:
  fixes F :: "slp_point \<Rightarrow> ennreal"
    and g :: "real \<Rightarrow> slp_point \<Rightarrow> complex"
    and h :: "slp_point \<Rightarrow> complex"
  assumes F_finite: "AE x in lborel. F x < top"
    and F_real_integrable: "integrable lborel (\<lambda>x. enn2real (F x))"
    and g_measurable: "\<And>tau. g tau \<in> borel_measurable lborel"
    and h_measurable: "h \<in> borel_measurable lborel"
    and uniform_convergence: "uniform_limit UNIV g h at_top"
  shows
    "((\<lambda>tau. \<integral>\<^sup>+ x.
        F x * ennreal (norm (g tau x - h x)) \<partial>lborel)
      \<longlongrightarrow> 0) at_top"
proof -
  have real_weight_limit:
      "((\<lambda>tau. \<integral>\<^sup>+ x.
          ennreal (enn2real (F x) * norm (g tau x - h x)) \<partial>lborel)
        \<longlongrightarrow> 0) at_top"
    by (rule
        slp_nonnegative_integrable_uniform_difference_nn_integral_tendsto_zero[
          OF F_real_integrable _ g_measurable h_measurable
            uniform_convergence]) simp
  have integral_identity:
      "(\<integral>\<^sup>+ x. F x * ennreal (norm (g tau x - h x)) \<partial>lborel) =
        (\<integral>\<^sup>+ x. ennreal
          (enn2real (F x) * norm (g tau x - h x)) \<partial>lborel)"
    for tau
  proof (rule nn_integral_cong_AE)
    show "AE x in lborel.
        F x * ennreal (norm (g tau x - h x)) =
          ennreal (enn2real (F x) * norm (g tau x - h x))"
      using F_finite
    proof eventually_elim
      fix x
      assume F_x_finite: "F x < top"
      show "F x * ennreal (norm (g tau x - h x)) =
          ennreal (enn2real (F x) * norm (g tau x - h x))"
        using F_x_finite
        by (simp add: ennreal_mult)
    qed
  qed
  show ?thesis
    using real_weight_limit by (simp only: integral_identity)
qed

end
