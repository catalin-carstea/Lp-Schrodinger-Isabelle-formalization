theory Inverse_Schrodinger_Lp_Positive_Ennreal_Lp
  imports Inverse_Schrodinger_Lp_Born_One_Sided_Terminal_HLS
begin

section \<open>Positive extended-real plane Lp data\<close>

definition slp_positive_ennreal_lp_on_plane ::
    "real \<Rightarrow> (slp_point \<Rightarrow> ennreal) \<Rightarrow> bool"
where
  "slp_positive_ennreal_lp_on_plane p F \<longleftrightarrow>
    F \<in> borel_measurable lborel \<and>
    (AE x in lborel. F x < top) \<and>
    integrable lborel (\<lambda>x. enn2real (F x) powr p)"

lemma slp_positive_ennreal_lp_from_real:
  assumes g_lp: "aim_real_lp_on_plane p g"
    and g_nonnegative: "AE x in lborel. 0 \<le> g x"
  shows
    "slp_positive_ennreal_lp_on_plane p (\<lambda>x. ennreal (g x))"
proof -
  have g_measurable: "g \<in> borel_measurable lborel"
    using g_lp unfolding aim_real_lp_on_plane_def by blast
  have g_power_integrable:
    "integrable lborel (\<lambda>x. abs (g x) powr p)"
    using g_lp unfolding aim_real_lp_on_plane_def by blast
  have lifted_measurable:
    "(\<lambda>x. ennreal (g x)) \<in> borel_measurable lborel"
    using g_measurable by measurable
  have lifted_finite: "AE x in lborel. ennreal (g x) < top"
    by simp
  have lifted_power_measurable:
    "(\<lambda>x. enn2real (ennreal (g x)) powr p)
      \<in> borel_measurable lborel"
    using g_measurable by measurable
  have lifted_power_integrable:
    "integrable lborel (\<lambda>x. enn2real (ennreal (g x)) powr p)"
    by (rule integrable_cong_AE_imp[OF g_power_integrable
          lifted_power_measurable])
      (use g_nonnegative in eventually_elim; simp)
  show ?thesis
    unfolding slp_positive_ennreal_lp_on_plane_def
    using lifted_measurable lifted_finite lifted_power_integrable by blast
qed

lemma slp_positive_ennreal_lp_product:
  assumes a_positive: "0 < a"
    and q_scale: "1 < q / a"
    and r_scale: "1 < r / a"
    and conjugate_scales: "1 / (q / a) + 1 / (r / a) = 1"
    and F_lp: "slp_positive_ennreal_lp_on_plane q F"
    and G_lp: "slp_positive_ennreal_lp_on_plane r G"
  shows
    "slp_positive_ennreal_lp_on_plane a (\<lambda>x. F x * G x)"
proof -
  have F_measurable: "F \<in> borel_measurable lborel"
    and F_finite: "AE x in lborel. F x < top"
    and F_power_integrable:
      "integrable lborel (\<lambda>x. enn2real (F x) powr q)"
    using F_lp unfolding slp_positive_ennreal_lp_on_plane_def by blast+
  have G_measurable: "G \<in> borel_measurable lborel"
    and G_finite: "AE x in lborel. G x < top"
    and G_power_integrable:
      "integrable lborel (\<lambda>x. enn2real (G x) powr r)"
    using G_lp unfolding slp_positive_ennreal_lp_on_plane_def by blast+
  have product_measurable:
    "(\<lambda>x. F x * G x) \<in> borel_measurable lborel"
    using F_measurable G_measurable by measurable
  have product_finite: "AE x in lborel. F x * G x < top"
    using F_finite G_finite
  proof eventually_elim
    fix x :: slp_point
    assume "F x < top" and "G x < top"
    then show "F x * G x < top"
      by (simp add: ennreal_mult_less_top)
  qed
  let ?Q = "q / a"
  let ?S = "r / a"
  let ?majorant = "\<lambda>x.
    enn2real (F x) powr q / ?Q + enn2real (G x) powr r / ?S"
  have Q_nonzero: "?Q \<noteq> 0" and S_nonzero: "?S \<noteq> 0"
    using q_scale r_scale by linarith+
  have Q_positive: "0 < ?Q" and S_positive: "0 < ?S"
    using q_scale r_scale by linarith+
  have majorant_integrable: "integrable lborel ?majorant"
    using F_power_integrable G_power_integrable Q_nonzero S_nonzero
    by simp
  have product_power_measurable:
    "(\<lambda>x. enn2real (F x * G x) powr a)
      \<in> borel_measurable lborel"
    using product_measurable by measurable
  have product_power_integrable:
    "integrable lborel (\<lambda>x. enn2real (F x * G x) powr a)"
  proof (rule Bochner_Integration.integrable_bound[OF majorant_integrable
        product_power_measurable])
    show "AE x in lborel.
        norm (enn2real (F x * G x) powr a) \<le> norm (?majorant x)"
    proof (rule AE_I2)
      fix x :: slp_point
      have scale_products: "a * ?Q = q" "a * ?S = r"
        using a_positive by simp_all
      have young:
        "(enn2real (F x) powr a) * (enn2real (G x) powr a) \<le>
          (enn2real (F x) powr a) powr ?Q / ?Q +
          (enn2real (G x) powr a) powr ?S / ?S"
        by (rule Youngs_inequality[OF q_scale r_scale conjugate_scales])
          simp_all
      have F_term_nonnegative:
          "0 \<le> enn2real (F x) powr q / ?Q"
      proof (rule divide_nonneg_pos)
        show "0 \<le> enn2real (F x) powr q" by simp
        show "0 < ?Q" using Q_positive .
      qed
      have G_term_nonnegative:
          "0 \<le> enn2real (G x) powr r / ?S"
      proof (rule divide_nonneg_pos)
        show "0 \<le> enn2real (G x) powr r" by simp
        show "0 < ?S" using S_positive .
      qed
      have majorant_nonnegative: "0 \<le> ?majorant x"
        using F_term_nonnegative G_term_nonnegative by simp
      show "norm (enn2real (F x * G x) powr a) \<le>
          norm (?majorant x)"
        using young majorant_nonnegative a_positive
        by (simp add: enn2real_mult powr_mult powr_powr scale_products)
    qed
  qed
  show ?thesis
    unfolding slp_positive_ennreal_lp_on_plane_def
    using product_measurable product_finite product_power_integrable by blast
qed

end
