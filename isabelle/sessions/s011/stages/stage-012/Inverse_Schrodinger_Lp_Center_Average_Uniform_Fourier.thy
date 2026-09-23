theory Inverse_Schrodinger_Lp_Center_Average_Uniform_Fourier
  imports
    "Paper_Inverse_Schrodinger_Lp_Proof_Stage_012.Inverse_Schrodinger_Lp_Center_Average_Fourier_Inversion"
begin

hide_const (open) Commutative_Ring.norm

section \<open>Uniform center convergence with an integrable Fourier transform\<close>

lemma slp_fourier_transform_diff:
  fixes f g :: slp_scalar_field
  assumes f_integrable: "integrable lborel f" and g_integrable: "integrable lborel g"
  shows "slp_fourier_transform (\<lambda>x. f x - g x) xi =
    slp_fourier_transform f xi - slp_fourier_transform g xi"
  unfolding slp_fourier_transform_def
  by (simp only: right_diff_distrib Bochner_Integration.integral_diff[
      OF slp_fourier_integrand_integrable[OF f_integrable]
        slp_fourier_integrand_integrable[OF g_integrable]])


lemma slp_center_multiplier_l1_error_tendsto_zero:
  fixes g :: slp_scalar_field
  assumes g_integrable: "integrable lborel g"
  shows "((\<lambda>tau. integral\<^sup>L lborel
    (\<lambda>xi. norm ((slp_center_fourier_multiplier tau xi - 1) * g xi)))
      \<longlongrightarrow> 0) at_top"
proof -
  let ?s = "\<lambda>tau xi. norm ((slp_center_fourier_multiplier tau xi - 1) * g xi)"
  have g_measurable: "g \<in> borel_measurable lborel" using g_integrable by measurable
  have target_measurable: "(\<lambda>xi::slp_point. (0::real)) \<in> borel_measurable lborel"
    by measurable
  have family_measurable: "?s tau \<in> borel_measurable lborel" for tau
    using g_measurable slp_center_fourier_multiplier_measurable[of tau] by measurable
  have bound_integrable: "integrable lborel (\<lambda>xi. 2 * norm (g xi))"
    using g_integrable by simp
  have pointwise: "AE xi in lborel. ((\<lambda>tau. ?s tau xi) \<longlongrightarrow> 0) at_top"
  proof (rule AE_I2)
    fix xi
    have limit: "((\<lambda>tau. (slp_center_fourier_multiplier tau xi - 1) * g xi)
        \<longlongrightarrow> (1 - 1) * g xi) at_top"
      using slp_center_fourier_multiplier_tendsto_one[of xi]
      by (intro tendsto_intros)
    show "((\<lambda>tau. ?s tau xi) \<longlongrightarrow> 0) at_top"
      using tendsto_norm[OF limit] by simp
  qed
  have bound: "norm (?s tau xi) \<le> 2 * norm (g xi)" for tau xi
  proof -
    have multiplier: "norm (slp_center_fourier_multiplier tau xi - 1) \<le> 2"
      using norm_triangle_ineq4[of "slp_center_fourier_multiplier tau xi" 1] by simp
    show ?thesis using mult_right_mono[OF multiplier norm_ge_zero[of "g xi"]]
      by (simp add: norm_mult)
  qed
  have eventual_bound:
      "\<forall>\<^sub>F tau in at_top. AE xi in lborel. norm (?s tau xi) \<le> 2 * norm (g xi)"
    using bound by simp
  have limit: "((\<lambda>tau. integral\<^sup>L lborel (?s tau)) \<longlongrightarrow>
      integral\<^sup>L lborel (\<lambda>xi::slp_point. (0::real))) at_top"
    by (rule integral_dominated_convergence_at_top[OF target_measurable
        family_measurable bound_integrable pointwise eventual_bound])
  show ?thesis using limit by simp
qed

context hormander_euclidean_l2_fourier_plancherel
begin

theorem slp_center_average_uniform_fourier_bound:
  fixes f :: slp_scalar_field
  assumes tau_positive: "0 < tau"
    and f_integrable: "integrable lborel f"
    and f_l2: "aim_complex_lp_on_plane 2 f"
    and fourier_integrable: "integrable lborel (slp_fourier_transform f)"
    and f_continuous: "continuous_on UNIV f"
  shows "norm (slp_center_average tau f c - f c) \<le>
    (integral\<^sup>L lborel (\<lambda>xi.
      norm ((slp_center_fourier_multiplier tau xi - 1) * slp_fourier_transform f xi))) /
        (2 * pi) ^ 2"
proof -
  let ?F = "slp_fourier_transform f"
  let ?g = "\<lambda>xi. slp_center_fourier_multiplier tau xi * ?F xi"
  let ?error = "\<lambda>xi. (slp_center_fourier_multiplier tau xi - 1) * ?F xi"
  let ?C = "(2 * pi) ^ 2"
  have C_positive: "0 < ?C" using pi_gt_zero by (intro zero_less_power mult_pos_pos) simp_all
  have product_integrable: "integrable lborel ?g"
    by (rule slp_center_fourier_product_integrable[OF fourier_integrable])
  have error_identity: "?error = (\<lambda>xi. ?g xi - ?F xi)"
    by (rule ext) (simp add: algebra_simps)
  have error_integrable: "integrable lborel ?error"
    unfolding error_identity
    by (rule Bochner_Integration.integrable_diff[OF product_integrable fourier_integrable])
  have transform_identity:
      "slp_fourier_transform ?error (-c) =
        of_real ?C * (slp_center_average tau f c - f c)"
  proof -
    have "slp_fourier_transform ?error (-c) =
        slp_fourier_transform ?g (-c) - slp_fourier_transform ?F (-c)"
      unfolding error_identity
      by (rule slp_fourier_transform_diff[OF product_integrable fourier_integrable])
    also have "... = of_real ?C * slp_center_average tau f c - of_real ?C * f c"
      using slp_center_average_fourier_inversion[OF tau_positive f_integrable fourier_integrable, of "-c"]
        slp_fourier_l1_double_transform[OF f_integrable f_l2 fourier_integrable f_continuous, of "-c"]
      by simp
    also have "... = of_real ?C * (slp_center_average tau f c - f c)"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have transform_bound: "norm (slp_fourier_transform ?error (-c)) \<le>
      integral\<^sup>L lborel (\<lambda>xi. norm (?error xi))"
    by (rule slp_fourier_transform_norm_bound[OF error_integrable])
  have scaled_bound: "?C * norm (slp_center_average tau f c - f c) \<le>
      integral\<^sup>L lborel (\<lambda>xi. norm (?error xi))"
    using transform_bound C_positive
    by (simp add: transform_identity norm_mult norm_power)
  show ?thesis using scaled_bound C_positive by (simp add: le_divide_eq mult.commute)
qed

theorem slp_center_average_uniform_limit_fourier_l1:
  fixes f :: slp_scalar_field
  assumes f_integrable: "integrable lborel f"
    and f_l2: "aim_complex_lp_on_plane 2 f"
    and fourier_integrable: "integrable lborel (slp_fourier_transform f)"
    and f_continuous: "continuous_on UNIV f"
  shows "uniform_limit UNIV (\<lambda>tau. slp_center_average tau f) f at_top"
proof -
  let ?mass = "\<lambda>tau. integral\<^sup>L lborel (\<lambda>xi.
    norm ((slp_center_fourier_multiplier tau xi - 1) * slp_fourier_transform f xi))"
  let ?bound = "\<lambda>tau. ?mass tau / (2 * pi) ^ 2"
  have mass_limit: "(?mass \<longlongrightarrow> 0) at_top"
    by (rule slp_center_multiplier_l1_error_tendsto_zero[OF fourier_integrable])
  have bound_limit: "(?bound \<longlongrightarrow> 0) at_top"
    using tendsto_divide[OF mass_limit tendsto_const] pi_gt_zero by simp
  show ?thesis
  proof (rule uniform_limitI)
    fix e :: real
    assume e_positive: "0 < e"
    have small: "\<forall>\<^sub>F tau in at_top. ?bound tau < e"
      by (rule order_tendstoD(2)[OF bound_limit e_positive])
    have positive: "\<forall>\<^sub>F tau::real in at_top. 0 < tau"
      by (rule eventually_gt_at_top)
    show "\<forall>\<^sub>F tau in at_top. \<forall>c\<in>UNIV. dist (slp_center_average tau f c) (f c) < e"
    proof (use small positive in eventually_elim)
      fix tau :: real
      assume bound_small: "?bound tau < e" and tau_positive: "0 < tau"
      have pointwise: "norm (slp_center_average tau f c - f c) \<le> ?bound tau" for c
        by (rule slp_center_average_uniform_fourier_bound[OF
            tau_positive f_integrable f_l2 fourier_integrable f_continuous])
      show "\<forall>c\<in>UNIV. dist (slp_center_average tau f c) (f c) < e"
        using pointwise bound_small by (simp add: dist_norm) (meson order_le_less_trans)
    qed
  qed
qed

end

end
