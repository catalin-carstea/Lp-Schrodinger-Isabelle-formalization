theory Inverse_Schrodinger_Lp_Real_Complex_L2_Pairing
  imports Inverse_Schrodinger_Lp_Born_One_Sided_All_Order_L2
begin

section \<open>Planar real--complex \(L^2\) pairing\<close>

lemma slp_real_complex_l2_pairing:
  fixes f :: "slp_point \<Rightarrow> real"
    and g :: "slp_point \<Rightarrow> complex"
  assumes f_l2: "aim_real_lp_on_plane 2 f"
    and g_l2: "aim_complex_lp_on_plane 2 g"
  shows product_integrable:
      "integrable lborel (\<lambda>x. of_real (f x) * g x)"
    and integral_norm_bound:
      "ennreal (Real_Vector_Spaces.norm (integral\<^sup>L lborel
          (\<lambda>x. of_real (f x) * g x)))
        \<le> (\<integral>\<^sup>+x. ennreal (abs (f x)) *
              ennreal (Real_Vector_Spaces.norm (g x))
              \<partial>lborel)"
    and integral_norm_square_bound:
      "ennreal (Real_Vector_Spaces.norm (integral\<^sup>L lborel
          (\<lambda>x. of_real (f x) * g x))) ^ 2
        \<le> (\<integral>\<^sup>+x. ennreal (abs (f x)) ^ 2 \<partial>lborel) *
          (\<integral>\<^sup>+x. ennreal (Real_Vector_Spaces.norm (g x)) ^ 2
            \<partial>lborel)"
proof -
  have f_measurable[measurable]: "f \<in> borel_measurable lborel"
    and f_power_integrable:
      "integrable lborel (\<lambda>x. abs (f x) powr 2)"
    using f_l2 unfolding aim_real_lp_on_plane_def by auto
  have g_measurable[measurable]: "g \<in> borel_measurable lborel"
    and g_power_integrable:
      "integrable lborel (\<lambda>x. Real_Vector_Spaces.norm (g x) powr 2)"
    using g_l2 unfolding aim_complex_lp_on_plane_def by auto
  have f_square_finite:
      "(\<integral>\<^sup>+x. ennreal (abs (f x)) ^ 2 \<partial>lborel) < top_class.top"
  proof -
    have bounded:
        "(\<integral>\<^sup>+x.
          ennreal (Real_Vector_Spaces.norm (abs (f x) powr 2))
          \<partial>lborel) < top_class.top"
      using f_power_integrable by (simp add: integrable_iff_bounded)
    show ?thesis
      using bounded by (simp add: powr_numeral ennreal_power)
  qed
  have g_square_finite:
      "(\<integral>\<^sup>+x. ennreal (Real_Vector_Spaces.norm (g x)) ^ 2
          \<partial>lborel) < top_class.top"
  proof -
    have bounded:
        "(\<integral>\<^sup>+x.
          ennreal (Real_Vector_Spaces.norm
            (Real_Vector_Spaces.norm (g x) powr 2))
          \<partial>lborel) < top_class.top"
      using g_power_integrable by (simp add: integrable_iff_bounded)
    show ?thesis
      using bounded by (simp add: powr_numeral ennreal_power)
  qed
  have cauchy_schwarz:
      "(\<integral>\<^sup>+x. ennreal (abs (f x)) *
          ennreal (Real_Vector_Spaces.norm (g x))
          \<partial>lborel) ^ 2
        \<le> (\<integral>\<^sup>+x. ennreal (abs (f x)) ^ 2 \<partial>lborel) *
          (\<integral>\<^sup>+x. ennreal (Real_Vector_Spaces.norm (g x)) ^ 2
            \<partial>lborel)"
    by (rule Cauchy_Schwarz_nn_integral; measurable)
  have product_norm_finite:
      "(\<integral>\<^sup>+x. ennreal (abs (f x)) *
          ennreal (Real_Vector_Spaces.norm (g x))
          \<partial>lborel) < top_class.top"
  proof -
    have square_finite:
        "(\<integral>\<^sup>+x. ennreal (abs (f x)) *
            ennreal (Real_Vector_Spaces.norm (g x))
            \<partial>lborel) ^ 2 < top_class.top"
      by (rule le_less_trans[OF cauchy_schwarz])
        (simp add: ennreal_mult_less_top f_square_finite g_square_finite)
    show ?thesis
      using square_finite by (simp add: power_less_top_ennreal)
  qed
  have product_measurable:
      "(\<lambda>x. of_real (f x) * g x) \<in> borel_measurable lborel"
    by measurable
  have product_norm:
      "\<And>x. ennreal (Real_Vector_Spaces.norm (of_real (f x) * g x)) =
        ennreal (abs (f x)) *
          ennreal (Real_Vector_Spaces.norm (g x))"
  proof -
    fix x
    have cast_product:
        "ennreal (abs (f x) * Real_Vector_Spaces.norm (g x)) =
          ennreal (abs (f x)) *
            ennreal (Real_Vector_Spaces.norm (g x))"
      by (rule ennreal_mult; simp only: abs_ge_zero norm_ge_zero)
    show "ennreal (Real_Vector_Spaces.norm (of_real (f x) * g x)) =
        ennreal (abs (f x)) *
          ennreal (Real_Vector_Spaces.norm (g x))"
      using cast_product by (simp only: norm_mult norm_of_real)
  qed
  show product_integrable:
      "integrable lborel (\<lambda>x. of_real (f x) * g x)"
    unfolding integrable_iff_bounded infinity_ennreal_def
  proof
    show "(\<lambda>x. of_real (f x) * g x) \<in> borel_measurable lborel"
      by (rule product_measurable)
    show "(\<integral>\<^sup>+x.
          ennreal (Real_Vector_Spaces.norm (of_real (f x) * g x))
          \<partial>lborel) < top_class.top"
      using product_norm_finite by (simp only: product_norm)
  qed
  have norm_bound:
      "ennreal (Real_Vector_Spaces.norm (integral\<^sup>L lborel
          (\<lambda>x. of_real (f x) * g x)))
        \<le> (\<integral>\<^sup>+x. ennreal (abs (f x)) *
              ennreal (Real_Vector_Spaces.norm (g x))
              \<partial>lborel)"
    using Bochner_Integration.integral_norm_bound_ennreal[OF product_integrable]
    by (simp only: product_norm)
  show "ennreal (Real_Vector_Spaces.norm (integral\<^sup>L lborel
          (\<lambda>x. of_real (f x) * g x)))
        \<le> (\<integral>\<^sup>+x. ennreal (abs (f x)) *
              ennreal (Real_Vector_Spaces.norm (g x))
              \<partial>lborel)"
    by (rule norm_bound)
  have norm_square:
      "ennreal (Real_Vector_Spaces.norm (integral\<^sup>L lborel
          (\<lambda>x. of_real (f x) * g x))) ^ 2
        \<le> (\<integral>\<^sup>+x. ennreal (abs (f x)) *
              ennreal (Real_Vector_Spaces.norm (g x))
              \<partial>lborel) ^ 2"
    by (rule power_mono[OF norm_bound]) simp
  show "ennreal (Real_Vector_Spaces.norm (integral\<^sup>L lborel
          (\<lambda>x. of_real (f x) * g x))) ^ 2
        \<le> (\<integral>\<^sup>+x. ennreal (abs (f x)) ^ 2 \<partial>lborel) *
          (\<integral>\<^sup>+x. ennreal (Real_Vector_Spaces.norm (g x)) ^ 2
            \<partial>lborel)"
  proof -
    have "ennreal (Real_Vector_Spaces.norm (integral\<^sup>L lborel
          (\<lambda>x. of_real (f x) * g x))) ^ 2
        \<le> (\<integral>\<^sup>+x. ennreal (abs (f x)) *
              ennreal (Real_Vector_Spaces.norm (g x))
              \<partial>lborel) ^ 2"
      by (rule norm_square)
    also have "... \<le>
        (\<integral>\<^sup>+x. ennreal (abs (f x)) ^ 2 \<partial>lborel) *
          (\<integral>\<^sup>+x. ennreal (Real_Vector_Spaces.norm (g x)) ^ 2
            \<partial>lborel)"
      by (rule cauchy_schwarz)
    finally show ?thesis .
  qed
qed

end
