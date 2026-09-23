theory Inverse_Schrodinger_Lp_Nonnegative_L2_Product
  imports Inverse_Schrodinger_Lp_Born_One_Sided_Square_Recurrence_HLS
begin

section \<open>Finite product integrals for nonnegative real \(L^2\) fields\<close>

lemma slp_nn_integral_product_lt_top_of_real_l2:
  fixes f g :: "slp_point \<Rightarrow> real"
  assumes f_l2: "aim_real_lp_on_plane 2 f"
    and g_l2: "aim_real_lp_on_plane 2 g"
    and f_nonnegative: "\<And>x. 0 \<le> f x"
    and g_nonnegative: "\<And>x. 0 \<le> g x"
  shows
    "(\<integral>\<^sup>+x. ennreal (f x) * ennreal (g x) \<partial>lborel) < top"
proof -
  have f_measurable[measurable]: "f \<in> borel_measurable lborel"
    and f_power_integrable:
      "integrable lborel (\<lambda>x. abs (f x) powr 2)"
    using f_l2 unfolding aim_real_lp_on_plane_def by auto
  have g_measurable[measurable]: "g \<in> borel_measurable lborel"
    and g_power_integrable:
      "integrable lborel (\<lambda>x. abs (g x) powr 2)"
    using g_l2 unfolding aim_real_lp_on_plane_def by auto
  have f_square_finite:
      "(\<integral>\<^sup>+x. ennreal (f x) ^ 2 \<partial>lborel) < top"
  proof -
    have bounded:
        "(\<integral>\<^sup>+x.
          ennreal (norm (abs (f x) powr 2)) \<partial>lborel) < top"
      using f_power_integrable by (simp add: integrable_iff_bounded)
    show ?thesis
      using bounded
      by (simp add: powr_numeral f_nonnegative ennreal_power)
  qed
  have g_square_finite:
      "(\<integral>\<^sup>+x. ennreal (g x) ^ 2 \<partial>lborel) < top"
  proof -
    have bounded:
        "(\<integral>\<^sup>+x.
          ennreal (norm (abs (g x) powr 2)) \<partial>lborel) < top"
      using g_power_integrable by (simp add: integrable_iff_bounded)
    show ?thesis
      using bounded
      by (simp add: powr_numeral g_nonnegative ennreal_power)
  qed
  have cauchy_schwarz:
      "(\<integral>\<^sup>+x. ennreal (f x) * ennreal (g x)
          \<partial>lborel) ^ 2 \<le>
        (\<integral>\<^sup>+x. ennreal (f x) ^ 2 \<partial>lborel) *
        (\<integral>\<^sup>+x. ennreal (g x) ^ 2 \<partial>lborel)"
    by (rule Cauchy_Schwarz_nn_integral; measurable)
  have square_finite:
      "(\<integral>\<^sup>+x. ennreal (f x) * ennreal (g x)
          \<partial>lborel) ^ 2 < top"
    by (rule le_less_trans[OF cauchy_schwarz])
      (simp add: ennreal_mult_less_top f_square_finite g_square_finite)
  show ?thesis
    using square_finite by (simp add: power_less_top_ennreal)
qed

end
