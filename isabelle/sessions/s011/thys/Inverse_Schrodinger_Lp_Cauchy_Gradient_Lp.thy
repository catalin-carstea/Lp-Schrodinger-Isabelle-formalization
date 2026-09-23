theory Inverse_Schrodinger_Lp_Cauchy_Gradient_Lp
  imports Inverse_Schrodinger_Lp_Cauchy_Weak_Derivative_Conjugate
begin

section \<open>Elementary closure of the explicit planar \<open>L^p\<close> predicate\<close>

lemma slp_norm_add_powr_bound:
  assumes p_nonnegative: "0 \<le> p"
  shows "norm (z + w) powr p \<le>
    2 powr p * (norm z powr p + norm w powr p)"
proof (cases "norm z \<le> norm w")
  case True
  have norm_bound: "norm (z + w) \<le> 2 * norm w"
    using norm_triangle_ineq[of z w] True by linarith
  have power_bound:
    "norm (z + w) powr p \<le> (2 * norm w) powr p"
    by (rule powr_mono2[OF p_nonnegative]) (use norm_bound in auto)
  have factor_bound:
    "2 powr p * norm w powr p \<le>
      2 powr p * (norm z powr p + norm w powr p)"
    by (intro mult_left_mono) simp_all
  show ?thesis
    using power_bound factor_bound
    by (simp only: powr_mult)
next
  case False
  have norm_bound: "norm (z + w) \<le> 2 * norm z"
    using norm_triangle_ineq[of z w] False by linarith
  have power_bound:
    "norm (z + w) powr p \<le> (2 * norm z) powr p"
    by (rule powr_mono2[OF p_nonnegative]) (use norm_bound in auto)
  have factor_bound:
    "2 powr p * norm z powr p \<le>
      2 powr p * (norm z powr p + norm w powr p)"
    by (intro mult_left_mono) simp_all
  show ?thesis
    using power_bound factor_bound
    by (simp only: powr_mult)
qed

lemma aim_complex_lp_on_plane_add:
  assumes p_positive: "0 < p"
    and f_lp: "aim_complex_lp_on_plane p f"
    and g_lp: "aim_complex_lp_on_plane p g"
  shows "aim_complex_lp_on_plane p (\<lambda>x. f x + g x)"
proof -
  have f_measurable: "f \<in> borel_measurable lborel"
    and f_power_integrable:
      "integrable lborel (\<lambda>x. norm (f x) powr p)"
    using f_lp unfolding aim_complex_lp_on_plane_def by auto
  have g_measurable: "g \<in> borel_measurable lborel"
    and g_power_integrable:
      "integrable lborel (\<lambda>x. norm (g x) powr p)"
    using g_lp unfolding aim_complex_lp_on_plane_def by auto
  have sum_measurable:
    "(\<lambda>x. f x + g x) \<in> borel_measurable lborel"
    using f_measurable g_measurable by measurable
  have sum_power_measurable:
    "(\<lambda>x. norm (f x + g x) powr p) \<in> borel_measurable lborel"
    using sum_measurable by measurable
  have majorant_integrable:
    "integrable lborel
      (\<lambda>x. 2 powr p *
        (norm (f x) powr p + norm (g x) powr p))"
  proof (rule integrable_mult_right)
    assume "2 powr p \<noteq> 0"
    show "integrable lborel
      (\<lambda>x. norm (f x) powr p + norm (g x) powr p)"
      by (rule Bochner_Integration.integrable_add[OF
            f_power_integrable g_power_integrable])
  qed
  have pointwise_bound:
    "AE x in lborel.
      norm (norm (f x + g x) powr p) \<le>
        norm (2 powr p *
          (norm (f x) powr p + norm (g x) powr p))"
  proof (rule AE_I2)
    fix x
    have bound:
      "norm (f x + g x) powr p \<le>
        2 powr p *
          (norm (f x) powr p + norm (g x) powr p)"
      by (rule slp_norm_add_powr_bound) (use p_positive in simp)
    have left_nonnegative: "0 \<le> norm (f x + g x) powr p"
      by simp
    have right_nonnegative:
      "0 \<le> 2 powr p *
        (norm (f x) powr p + norm (g x) powr p)"
      by (rule mult_nonneg_nonneg) simp_all
    show "norm (norm (f x + g x) powr p) \<le>
        norm (2 powr p *
          (norm (f x) powr p + norm (g x) powr p))"
      using bound left_nonnegative right_nonnegative by simp
  qed
  have sum_power_integrable:
    "integrable lborel (\<lambda>x. norm (f x + g x) powr p)"
    by (rule Bochner_Integration.integrable_bound[OF
          majorant_integrable sum_power_measurable pointwise_bound])
  show ?thesis
    unfolding aim_complex_lp_on_plane_def
    using sum_measurable sum_power_integrable by blast
qed

lemma aim_complex_lp_on_plane_uminus:
  assumes f_lp: "aim_complex_lp_on_plane p f"
  shows "aim_complex_lp_on_plane p (\<lambda>x. - f x)"
  using f_lp
  unfolding aim_complex_lp_on_plane_def
  by (auto intro!: borel_measurable_uminus)

lemma aim_complex_lp_on_plane_diff:
  assumes p_positive: "0 < p"
    and f_lp: "aim_complex_lp_on_plane p f"
    and g_lp: "aim_complex_lp_on_plane p g"
  shows "aim_complex_lp_on_plane p (\<lambda>x. f x - g x)"
proof -
  have minus_g_lp: "aim_complex_lp_on_plane p (\<lambda>x. - g x)"
    by (rule aim_complex_lp_on_plane_uminus[OF g_lp])
  have "aim_complex_lp_on_plane p (\<lambda>x. f x + (- g x))"
    by (rule aim_complex_lp_on_plane_add[OF p_positive f_lp minus_g_lp])
  then show ?thesis by simp
qed

lemma aim_complex_lp_on_plane_cmult_unit:
  assumes c_unit: "norm c = 1"
    and f_lp: "aim_complex_lp_on_plane p f"
  shows "aim_complex_lp_on_plane p (\<lambda>x. c * f x)"
proof -
  have f_measurable: "f \<in> borel_measurable lborel"
    and f_power_integrable:
      "integrable lborel (\<lambda>x. norm (f x) powr p)"
    using f_lp unfolding aim_complex_lp_on_plane_def by auto
  have scaled_measurable:
    "(\<lambda>x. c * f x) \<in> borel_measurable lborel"
    using f_measurable by measurable
  have scaled_power:
    "(\<lambda>x. norm (c * f x) powr p) =
      (\<lambda>x. norm (f x) powr p)"
  proof (rule ext)
    fix x
    show "norm (c * f x) powr p = norm (f x) powr p"
      using c_unit by (simp add: norm_mult)
  qed
  have scaled_power_integrable:
    "integrable lborel (\<lambda>x. norm (c * f x) powr p)"
    using f_power_integrable unfolding scaled_power .
  show ?thesis
    unfolding aim_complex_lp_on_plane_def
    using scaled_measurable scaled_power_integrable by blast
qed

section \<open>Both exact Cauchy gradients\<close>

definition slp_gradient_components_lp ::
  "real \<Rightarrow> slp_gradient_field \<Rightarrow> bool"
where
  "slp_gradient_components_lp p Du \<longleftrightarrow>
    aim_complex_lp_on_plane p (\<lambda>x. Du x $ 0) \<and>
    aim_complex_lp_on_plane p (\<lambda>x. Du x $ 1)"

context aim_planar_cauchy_beurling_derivatives
begin

theorem slp_both_cauchy_gradient_components_lp:
  assumes p_lower: "1 < (p::real)"
    and f_lp: "aim_complex_lp_on_plane p f"
  shows "slp_gradient_components_lp p (slp_dbar_inverse_gradient f) \<and>
    slp_gradient_components_lp p (slp_partial_inverse_gradient f)"
proof -
  obtain S_p::real where S_p_positive: "0 < S_p"
    and both_beurling:
      "\<And>f. aim_complex_lp_on_plane p f \<Longrightarrow>
        (AE z in lborel. slp_beurling_pv_exists f z) \<and>
        aim_complex_lp_on_plane p (slp_beurling_transform f) \<and>
        aim_complex_lp_norm p (slp_beurling_transform f)
          \<le> S_p * aim_complex_lp_norm p f \<and>
        (AE z in lborel. slp_opposite_beurling_pv_exists f z) \<and>
        aim_complex_lp_on_plane p (slp_opposite_beurling_transform f) \<and>
        aim_complex_lp_norm p (slp_opposite_beurling_transform f)
          \<le> S_p * aim_complex_lp_norm p f"
    using slp_both_beurling_lp p_lower by blast
  have p_positive: "0 < p"
    using p_lower by linarith
  have direct_lp:
    "aim_complex_lp_on_plane p (slp_beurling_transform f)"
    using both_beurling[OF f_lp] by blast
  have opposite_lp:
    "aim_complex_lp_on_plane p (slp_opposite_beurling_transform f)"
    using both_beurling[OF f_lp] by blast
  have dbar_0:
    "aim_complex_lp_on_plane p
      (\<lambda>x. slp_dbar_inverse_gradient f x $ 0)"
    using aim_complex_lp_on_plane_add[OF p_positive f_lp direct_lp]
    by simp
  have dbar_difference:
    "aim_complex_lp_on_plane p
      (\<lambda>x. slp_beurling_transform f x - f x)"
    by (rule aim_complex_lp_on_plane_diff[OF p_positive direct_lp f_lp])
  have dbar_1:
    "aim_complex_lp_on_plane p
      (\<lambda>x. slp_dbar_inverse_gradient f x $ 1)"
    using aim_complex_lp_on_plane_cmult_unit[where c = "\<i>"
        and f = "\<lambda>x. slp_beurling_transform f x - f x",
        OF _ dbar_difference]
    by simp
  have partial_0:
    "aim_complex_lp_on_plane p
      (\<lambda>x. slp_partial_inverse_gradient f x $ 0)"
    using aim_complex_lp_on_plane_add[OF p_positive f_lp opposite_lp]
    by simp
  have partial_difference:
    "aim_complex_lp_on_plane p
      (\<lambda>x. f x - slp_opposite_beurling_transform f x)"
    by (rule aim_complex_lp_on_plane_diff[OF p_positive f_lp opposite_lp])
  have partial_1:
    "aim_complex_lp_on_plane p
      (\<lambda>x. slp_partial_inverse_gradient f x $ 1)"
    using aim_complex_lp_on_plane_cmult_unit[where c = "\<i>"
        and f = "\<lambda>x. f x - slp_opposite_beurling_transform f x",
        OF _ partial_difference]
    by simp
  show ?thesis
    unfolding slp_gradient_components_lp_def
    using dbar_0 dbar_1 partial_0 partial_1 by blast
qed

theorem slp_both_cauchy_weak_gradients_with_lp_components:
  assumes p_lower: "1 < (p::real)"
    and f_lp: "aim_complex_lp_on_plane p f"
    and f_support: "bounded {x. f x \<noteq> 0}"
  shows "slp_weak_gradient_on UNIV
      (slp_dbar_inverse f) (slp_dbar_inverse_gradient f) \<and>
    slp_gradient_components_lp p (slp_dbar_inverse_gradient f) \<and>
    slp_weak_gradient_on UNIV
      (slp_partial_inverse f) (slp_partial_inverse_gradient f) \<and>
    slp_gradient_components_lp p (slp_partial_inverse_gradient f)"
  using slp_dbar_inverse_weak_gradient[OF p_lower f_lp f_support]
    slp_partial_inverse_weak_gradient[OF p_lower f_lp f_support]
    slp_both_cauchy_gradient_components_lp[OF p_lower f_lp]
  by blast

end

end
