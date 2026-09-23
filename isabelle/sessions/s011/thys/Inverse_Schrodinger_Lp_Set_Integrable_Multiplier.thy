theory Inverse_Schrodinger_Lp_Set_Integrable_Multiplier
  imports Inverse_Schrodinger_Lp_Local_L1_Integrability
begin

section \<open>Bounded multipliers for ordinary set integrability\<close>

lemma slp_set_integrable_mult_bounded:
  fixes f g :: slp_scalar_field
  assumes X_measurable: "X \<in> sets lborel"
    and f_integrable: "set_integrable lborel X f"
    and f_measurable: "f \<in> borel_measurable lborel"
    and g_measurable: "g \<in> borel_measurable lborel"
    and M_nonnegative: "0 \<le> M"
    and g_bound: "\<And>x. x \<in> X \<Longrightarrow> norm (g x) \<le> M"
  shows "set_integrable lborel X (\<lambda>x. f x * g x)"
proof -
  have majorant_integrable:
    "set_integrable lborel X (\<lambda>x. M *\<^sub>R f x)"
    using f_integrable by auto
  have product_set_measurable:
    "set_borel_measurable lborel X (\<lambda>x. f x * g x)"
    unfolding set_borel_measurable_def
    using X_measurable f_measurable g_measurable by measurable
  show ?thesis
  proof (rule set_integrable_bound[OF
        majorant_integrable product_set_measurable])
    show "AE x in lborel.
        x \<in> X \<longrightarrow>
          norm (f x * g x) \<le> norm (M *\<^sub>R f x)"
    proof (rule AE_I2)
      fix x
      show "x \<in> X \<longrightarrow>
          norm (f x * g x) \<le> norm (M *\<^sub>R f x)"
      proof
        assume x_in: "x \<in> X"
        have "norm (f x * g x) = norm (f x) * norm (g x)"
          by (simp add: norm_mult)
        also have "... \<le> norm (f x) * M"
          by (rule mult_left_mono[OF g_bound[OF x_in]]) simp
        also have "... = norm (M *\<^sub>R f x)"
          using M_nonnegative by (simp add: mult.commute)
        finally show "norm (f x * g x) \<le> norm (M *\<^sub>R f x)" .
      qed
    qed
  qed
qed

theorem aim_complex_lp_on_plane_mult_set_integrable_compact:
  fixes f g :: slp_scalar_field
  assumes p_at_least_one: "1 \<le> p"
    and K_compact: "compact K"
    and f_lp: "aim_complex_lp_on_plane p f"
    and g_measurable: "g \<in> borel_measurable lborel"
    and g_continuous: "continuous_on K g"
  shows "set_integrable lborel K (\<lambda>x. f x * g x)"
proof -
  have K_closed: "closed K"
    by (rule compact_imp_closed[OF K_compact])
  have K_measurable: "K \<in> sets lborel"
    using K_closed by measurable
  have K_bounded: "bounded K"
    by (rule compact_imp_bounded[OF K_compact])
  have f_integrable: "set_integrable lborel K f"
    by (rule aim_complex_lp_on_plane_set_integrable_bounded[OF
          p_at_least_one K_measurable K_bounded f_lp])
  have f_measurable: "f \<in> borel_measurable lborel"
    using f_lp unfolding aim_complex_lp_on_plane_def by auto
  have image_bounded: "bounded (g ` K)"
    by (rule compact_imp_bounded)
       (rule compact_continuous_image[OF g_continuous K_compact])
  then obtain B where B_bound: "\<And>x. x \<in> K \<Longrightarrow> norm (g x) \<le> B"
    unfolding bounded_iff by blast
  let ?M = "max 0 B"
  have M_nonnegative: "0 \<le> ?M"
    by simp
  have g_bound: "\<And>x. x \<in> K \<Longrightarrow> norm (g x) \<le> ?M"
    using B_bound by fastforce
  show ?thesis
    by (rule slp_set_integrable_mult_bounded[OF
          K_measurable f_integrable f_measurable g_measurable
          M_nonnegative g_bound])
qed

end
